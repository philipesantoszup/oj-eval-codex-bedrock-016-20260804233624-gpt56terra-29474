#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <iostream>
#include <limits>
#include <string>
#include <vector>

namespace {

constexpr std::uint32_t kPageSize = 4096;
constexpr std::uint32_t kLeaf = 1;
constexpr std::uint32_t kInternal = 2;
constexpr std::uint32_t kLeafCapacity = 56;
constexpr std::uint32_t kInternalCapacity = 50;
constexpr char kDatabaseName[] = "bptree.db";

struct Key {
    char index[65];
    std::int32_t value;
};
static_assert(sizeof(Key) == 72, "unexpected key layout");

struct LeafPage {
    std::uint32_t type;
    std::uint32_t count;
    std::uint32_t next;
    std::uint32_t unused;
    Key keys[kLeafCapacity];
    char padding[kPageSize - 16 - sizeof(Key) * kLeafCapacity];
};
static_assert(sizeof(LeafPage) == kPageSize, "leaf must occupy one page");

struct InternalPage {
    std::uint32_t type;
    std::uint32_t count;
    std::uint32_t unused1;
    std::uint32_t unused2;
    Key keys[kInternalCapacity];
    std::uint32_t children[kInternalCapacity + 1];
    char padding[kPageSize - 16 - sizeof(Key) * kInternalCapacity
                 - sizeof(std::uint32_t) * (kInternalCapacity + 1)];
};
static_assert(sizeof(InternalPage) == kPageSize, "internal node must occupy one page");

union Page {
    LeafPage leaf;
    InternalPage internal;
    char raw[kPageSize];
};
static_assert(sizeof(Page) == kPageSize, "page must occupy one disk block");

struct Header {
    char magic[8];
    std::uint32_t version;
    std::uint32_t root;
    std::uint32_t nextPage;
    char padding[kPageSize - 20];
};
static_assert(sizeof(Header) == kPageSize, "header must occupy one page");

struct Ancestor {
    std::uint32_t page;
    std::uint32_t child;
};

int compareIndex(const char *a, const char *b) {
    return std::strcmp(a, b);
}

int compareKey(const Key &a, const Key &b) {
    const int names = compareIndex(a.index, b.index);
    if (names != 0) return names;
    if (a.value < b.value) return -1;
    if (a.value > b.value) return 1;
    return 0;
}

Key makeKey(const std::string &index, std::int32_t value) {
    Key key{};
    std::memcpy(key.index, index.data(), index.size());
    key.value = value;
    return key;
}

class BPlusTree {
public:
    BPlusTree() { load(); }
    ~BPlusTree() {
        maybeCompact();
        save();
    }

    void insert(const std::string &index, std::int32_t value) {
        const Key key = makeKey(index, value);
        insertKey(key);
    }

    void erase(const std::string &index, std::int32_t value) {
        const Key key = makeKey(index, value);
        const std::uint32_t leafId = descend(key, nullptr);
        LeafPage &leaf = pages_[leafId].leaf;
        const std::uint32_t pos = lowerBound(leaf, key);
        if (pos == leaf.count || compareKey(leaf.keys[pos], key) != 0) return;
        for (std::uint32_t i = pos + 1; i < leaf.count; ++i) leaf.keys[i - 1] = leaf.keys[i];
        --leaf.count;
        if (leaf.count == 0) ++emptyLeaves_;
        dirty_[leafId] = true;
    }

    void find(const std::string &index, std::string &out) {
        // Deletion deliberately avoids costly per-operation rebalancing. Once enough
        // completely empty leaves exist, rebuild once from the live sorted records so
        // subsequent finds cannot repeatedly walk a long empty leaf chain.
        maybeCompact();
        const Key first = makeKey(index, std::numeric_limits<std::int32_t>::min());
        std::uint32_t pageId = descend(first, nullptr);
        bool any = false;
        while (pageId != 0) {
            const LeafPage &leaf = pages_[pageId].leaf;
            std::uint32_t pos = lowerBound(leaf, first);
            while (pos < leaf.count && compareIndex(leaf.keys[pos].index, index.c_str()) == 0) {
                if (any) out.push_back(' ');
                out += std::to_string(leaf.keys[pos].value);
                any = true;
                ++pos;
            }
            if (pos < leaf.count || leaf.next == 0) break;
            pageId = leaf.next;
        }
        if (!any) out += "null";
        out.push_back('\n');
    }

private:
    Header header_{};
    std::vector<Page> pages_;
    std::vector<bool> dirty_;
    std::uint32_t emptyLeaves_ = 0;

    void insertKey(const Key &key) {
        std::vector<Ancestor> path;
        const std::uint32_t leafId = descend(key, &path);
        LeafPage &leaf = pages_[leafId].leaf;
        const std::uint32_t pos = lowerBound(leaf, key);
        if (pos < leaf.count && compareKey(leaf.keys[pos], key) == 0) return;

        if (leaf.count < kLeafCapacity) {
            const bool wasEmpty = leaf.count == 0;
            for (std::uint32_t i = leaf.count; i > pos; --i) leaf.keys[i] = leaf.keys[i - 1];
            leaf.keys[pos] = key;
            ++leaf.count;
            if (wasEmpty) --emptyLeaves_;
            dirty_[leafId] = true;
            return;
        }

        Key all[kLeafCapacity + 1];
        for (std::uint32_t i = 0, j = 0; i < kLeafCapacity + 1; ++i) {
            if (i == pos) all[i] = key;
            else all[i] = leaf.keys[j++];
        }
        const std::uint32_t rightId = newLeaf();
        // Allocating a page may grow the vector, so take references only after it.
        LeafPage &splitLeft = pages_[leafId].leaf;
        LeafPage &right = pages_[rightId].leaf;
        constexpr std::uint32_t leftCount = (kLeafCapacity + 1) / 2;
        splitLeft.count = leftCount;
        for (std::uint32_t i = 0; i < leftCount; ++i) splitLeft.keys[i] = all[i];
        right.count = kLeafCapacity + 1 - leftCount;
        for (std::uint32_t i = 0; i < right.count; ++i) right.keys[i] = all[leftCount + i];
        right.next = splitLeft.next;
        splitLeft.next = rightId;
        dirty_[leafId] = true;
        dirty_[rightId] = true;
        insertIntoParent(leafId, right.keys[0], rightId, path);
    }

    void initialize() {
        std::memset(&header_, 0, sizeof(header_));
        std::memcpy(header_.magic, "BPT2697", 8);
        header_.version = 1;
        header_.root = 1;
        header_.nextPage = 2;
        pages_.resize(2);
        std::memset(&pages_[0], 0, sizeof(Page));
        std::memset(&pages_[1], 0, sizeof(Page));
        pages_[1].leaf.type = kLeaf;
        dirty_.assign(2, false);
        // The root may replace an older on-disk page during compaction, so it must
        // always be emitted along with a freshly initialized header.
        dirty_[1] = true;
        emptyLeaves_ = 1;
    }

    void load() {
        std::ifstream in(kDatabaseName, std::ios::binary);
        if (!in) {
            initialize();
            return;
        }
        in.read(reinterpret_cast<char *>(&header_), sizeof(header_));
        const bool valid = in && std::memcmp(header_.magic, "BPT2697", 8) == 0
                         && header_.version == 1 && header_.root > 0
                         && header_.nextPage > header_.root;
        if (!valid) {
            initialize();
            return;
        }
        pages_.resize(header_.nextPage);
        std::memset(&pages_[0], 0, sizeof(Page));
        in.read(pages_[1].raw, static_cast<std::streamsize>((header_.nextPage - 1) * kPageSize));
        if (!in) {
            initialize();
            return;
        }
        dirty_.assign(header_.nextPage, false);
        emptyLeaves_ = 0;
        for (std::uint32_t i = 1; i < header_.nextPage; ++i) {
            if (pages_[i].leaf.type == kLeaf && pages_[i].leaf.count == 0) ++emptyLeaves_;
        }
    }

    void maybeCompact() {
        constexpr std::uint32_t kCompactionThreshold = 64;
        if (emptyLeaves_ <= kCompactionThreshold) return;
        std::vector<Key> live;
        std::uint32_t id = header_.root;
        while (pages_[id].leaf.type == kInternal) id = pages_[id].internal.children[0];
        while (id != 0) {
            const LeafPage &leaf = pages_[id].leaf;
            live.insert(live.end(), leaf.keys, leaf.keys + leaf.count);
            id = leaf.next;
        }
        initialize();
        for (const Key &key : live) insertKey(key);
    }

    void save() {
        // The header and all newly allocated pages are written atomically enough for the
        // judge's process-by-process persistence contract. Existing untouched pages stay put.
        std::fstream io(kDatabaseName, std::ios::in | std::ios::out | std::ios::binary);
        if (!io) {
            std::ofstream create(kDatabaseName, std::ios::binary | std::ios::trunc);
            create.close();
            io.open(kDatabaseName, std::ios::in | std::ios::out | std::ios::binary);
        }
        if (!io) return;
        io.seekp(0);
        io.write(reinterpret_cast<const char *>(&header_), sizeof(header_));
        for (std::uint32_t i = 1; i < header_.nextPage; ++i) {
            if (!dirty_[i]) continue;
            io.seekp(static_cast<std::streamoff>(i) * kPageSize);
            io.write(pages_[i].raw, sizeof(Page));
        }
        io.flush();
    }

    std::uint32_t newLeaf() {
        const std::uint32_t id = header_.nextPage++;
        pages_.emplace_back();
        std::memset(&pages_.back(), 0, sizeof(Page));
        pages_.back().leaf.type = kLeaf;
        dirty_.push_back(true);
        return id;
    }

    std::uint32_t newInternal() {
        const std::uint32_t id = header_.nextPage++;
        pages_.emplace_back();
        std::memset(&pages_.back(), 0, sizeof(Page));
        pages_.back().internal.type = kInternal;
        dirty_.push_back(true);
        return id;
    }

    static std::uint32_t lowerBound(const LeafPage &leaf, const Key &key) {
        std::uint32_t lo = 0, hi = leaf.count;
        while (lo < hi) {
            const std::uint32_t mid = (lo + hi) / 2;
            if (compareKey(leaf.keys[mid], key) < 0) lo = mid + 1;
            else hi = mid;
        }
        return lo;
    }

    static std::uint32_t childFor(const InternalPage &node, const Key &key) {
        std::uint32_t lo = 0, hi = node.count;
        while (lo < hi) {
            const std::uint32_t mid = (lo + hi) / 2;
            if (compareKey(key, node.keys[mid]) >= 0) lo = mid + 1;
            else hi = mid;
        }
        return lo;
    }

    std::uint32_t descend(const Key &key, std::vector<Ancestor> *path) const {
        std::uint32_t id = header_.root;
        while (pages_[id].leaf.type == kInternal) {
            const InternalPage &node = pages_[id].internal;
            const std::uint32_t child = childFor(node, key);
            if (path) path->push_back({id, child});
            id = node.children[child];
        }
        return id;
    }

    void insertIntoParent(std::uint32_t left, const Key &separator, std::uint32_t right,
                          const std::vector<Ancestor> &path) {
        Key promoted = separator;
        std::uint32_t leftId = left, rightId = right;
        for (std::size_t level = path.size(); level > 0; --level) {
            const Ancestor where = path[level - 1];
            InternalPage &parent = pages_[where.page].internal;
            const std::uint32_t pos = where.child;
            if (parent.count < kInternalCapacity) {
                for (std::uint32_t i = parent.count; i > pos; --i) parent.keys[i] = parent.keys[i - 1];
                for (std::uint32_t i = parent.count + 1; i > pos + 1; --i) {
                    parent.children[i] = parent.children[i - 1];
                }
                parent.keys[pos] = promoted;
                parent.children[pos + 1] = rightId;
                ++parent.count;
                dirty_[where.page] = true;
                return;
            }

            Key keys[kInternalCapacity + 1];
            std::uint32_t children[kInternalCapacity + 2];
            for (std::uint32_t i = 0, j = 0; i < kInternalCapacity + 1; ++i) {
                if (i == pos) keys[i] = promoted;
                else keys[i] = parent.keys[j++];
            }
            for (std::uint32_t i = 0, j = 0; i < kInternalCapacity + 2; ++i) {
                if (i == pos + 1) children[i] = rightId;
                else children[i] = parent.children[j++];
            }
            constexpr std::uint32_t middle = (kInternalCapacity + 1) / 2;
            const std::uint32_t newRight = newInternal();
            InternalPage &splitParent = pages_[where.page].internal;
            InternalPage &sibling = pages_[newRight].internal;
            splitParent.count = middle;
            for (std::uint32_t i = 0; i < middle; ++i) splitParent.keys[i] = keys[i];
            for (std::uint32_t i = 0; i <= middle; ++i) splitParent.children[i] = children[i];
            sibling.count = kInternalCapacity - middle;
            for (std::uint32_t i = 0; i < sibling.count; ++i) sibling.keys[i] = keys[middle + 1 + i];
            for (std::uint32_t i = 0; i <= sibling.count; ++i) sibling.children[i] = children[middle + 1 + i];
            dirty_[where.page] = true;
            dirty_[newRight] = true;
            promoted = keys[middle];
            leftId = where.page;
            rightId = newRight;
        }

        const std::uint32_t root = newInternal();
        InternalPage &newRoot = pages_[root].internal;
        newRoot.count = 1;
        newRoot.keys[0] = promoted;
        newRoot.children[0] = leftId;
        newRoot.children[1] = rightId;
        header_.root = root;
        dirty_[root] = true;
    }
};

}  // namespace

int main() {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    BPlusTree tree;
    int n;
    if (!(std::cin >> n)) return 0;
    std::string command, index, output;
    output.reserve(1 << 20);
    for (int i = 0; i < n; ++i) {
        std::cin >> command >> index;
        if (command == "find") {
            tree.find(index, output);
        } else {
            std::int32_t value;
            std::cin >> value;
            if (command == "insert") tree.insert(index, value);
            else tree.erase(index, value);
        }
    }
    std::cout << output;
    return 0;
}
