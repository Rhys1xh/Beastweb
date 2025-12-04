// BeastWeb.cpp - ULTIMATE SINGLE-FILE HTTP SERVER
// Compile: cl /std:c++20 /O2 /MT /EHsc /D_WIN32_WINNT=0x0A00 BeastWeb.cpp ws2_32.lib mswsock.lib

#define _WIN32_WINNT 0x0A00
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#define _CRT_SECURE_NO_WARNINGS
#define _WINSOCK_DEPRECATED_NO_WARNINGS

#include <windows.h>
#include <winsock2.h>
#include <mswsock.h>
#include <ws2tcpip.h>
#include <intrin.h>
#include <psapi.h>
#include <processthreadsapi.h>
#include <sysinfoapi.h>
#include <memoryapi.h>
#include <errhandlingapi.h>
#include <atomic>
#include <memory>
#include <functional>
#include <string>
#include <string_view>
#include <vector>
#include <unordered_map>
#include <map>
#include <queue>
#include <thread>
#include <mutex>
#include <shared_mutex>
#include <condition_variable>
#include <chrono>
#include <algorithm>
#include <iostream>
#include <iomanip>
#include <sstream>
#include <fstream>
#include <charconv>
#include <array>
#include <span>
#include <optional>
#include <cstring>
#include <cmath>
#include <cctype>

#pragma comment(lib, "ws2_32.lib")
#pragma comment(lib, "mswsock.lib")

// ============================================================================
// CONSTANTS
// ============================================================================
constexpr size_t MAX_WORKER_THREADS = 64;
constexpr size_t MAX_CONCURRENT_CONNECTIONS = 1000000;
constexpr size_t IOCP_COMPLETION_THREADS = 8;
constexpr size_t BUFFER_SIZE = 65536;
constexpr size_t MAX_REQUEST_SIZE = 16777216;
constexpr size_t RESPONSE_CACHE_ENTRIES = 100000;
constexpr bool USE_HUGE_PAGES = true;
constexpr bool USE_AVX2_OPTIMIZATIONS = true;

// ============================================================================
// PERFORMANCE MACROS
// ============================================================================
#ifdef _MSC_VER
#define FORCE_INLINE __forceinline
#define NO_INLINE __declspec(noinline)
#define CACHE_ALIGN __declspec(align(64))
#define LIKELY(x) (x)
#define UNLIKELY(x) (x)
#define ASSUME(cond) __assume(cond)
#define PREFETCH(addr) _mm_prefetch((const char*)(addr), _MM_HINT_T0)
#else
#define FORCE_INLINE __attribute__((always_inline))
#define NO_INLINE __attribute__((noinline))
#define CACHE_ALIGN alignas(64)
#define LIKELY(x) __builtin_expect(!!(x), 1)
#define UNLIKELY(x) __builtin_expect(!!(x), 0)
#define ASSUME(cond) do { if (!(cond)) __builtin_unreachable(); } while(0)
#define PREFETCH(addr) __builtin_prefetch(addr)
#endif

// ============================================================================
// POWERFUL HTTP PARSER (PROFESSIONAL GRADE)
// ============================================================================
class CACHE_ALIGN HttpParser {
private:
    enum class State : uint8_t {
        START, METHOD, SPACE_BEFORE_URI, URI, HTTP_VERSION_H, HTTP_VERSION_T1,
        HTTP_VERSION_T2, HTTP_VERSION_P, HTTP_VERSION_SLASH,
        HTTP_VERSION_MAJOR_START, HTTP_VERSION_MAJOR, HTTP_VERSION_MINOR_START,
        HTTP_VERSION_MINOR, HEADER_LINE_START, HEADER_NAME, HEADER_VALUE_START,
        HEADER_VALUE, EXPECTING_NEWLINE_1, EXPECTING_NEWLINE_2, BODY, COMPLETE
    };

    State state_{ State::START };
    std::string_view method_;
    std::string_view uri_;
    std::string_view body_;
    int major_version_{ 1 };
    int minor_version_{ 1 };
    bool keep_alive_{ false };
    size_t content_length_{ 0 };
    size_t body_bytes_received_{ 0 };

    std::string current_header_name_;
    std::unordered_map<std::string, std::string> headers_;

    // Buffer tracking
    const char* buffer_start_{ nullptr };
    const char* cursor_{ nullptr };
    const char* buffer_end_{ nullptr };

    // Helper methods
    FORCE_INLINE bool is_token_char(char c) const noexcept {
        // RFC 7230 token characters
        return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
            (c >= '0' && c <= '9') || c == '!' || c == '#' || c == '$' ||
            c == '%' || c == '&' || c == '\'' || c == '*' || c == '+' ||
            c == '-' || c == '.' || c == '^' || c == '_' || c == '`' ||
            c == '|' || c == '~';
    }

    FORCE_INLINE bool is_space(char c) const noexcept {
        return c == ' ' || c == '\t';
    }

    FORCE_INLINE bool is_digit(char c) const noexcept {
        return c >= '0' && c <= '9';
    }

public:
    HttpParser() = default;

    void reset() noexcept {
        state_ = State::START;
        method_ = std::string_view();
        uri_ = std::string_view();
        body_ = std::string_view();
        major_version_ = 1;
        minor_version_ = 1;
        keep_alive_ = false;
        content_length_ = 0;
        body_bytes_received_ = 0;
        current_header_name_.clear();
        headers_.clear();
        buffer_start_ = cursor_ = buffer_end_ = nullptr;
    }

    FORCE_INLINE bool parse(const char* data, size_t length) noexcept {
        if (!data || length == 0) return false;

        buffer_start_ = data;
        cursor_ = data;
        buffer_end_ = data + length;

        while (cursor_ < buffer_end_ && state_ != State::COMPLETE) {
            char c = *cursor_++;

            switch (state_) {
            case State::START:
                if (is_token_char(c)) {
                    const char* method_start = cursor_ - 1;
                    // Fast method detection
                    switch (c) {
                    case 'G': method_ = "GET"; break;
                    case 'P':
                        if (cursor_ < buffer_end_) {
                            if (*cursor_ == 'O') method_ = "POST";
                            else if (*cursor_ == 'U') method_ = "PUT";
                            else if (*cursor_ == 'A') method_ = "PATCH";
                        }
                        break;
                    case 'D': method_ = "DELETE"; break;
                    case 'H': method_ = "HEAD"; break;
                    case 'O': method_ = "OPTIONS"; break;
                    }
                    state_ = State::METHOD;
                    // Skip rest of method
                    while (cursor_ < buffer_end_ && is_token_char(*cursor_)) ++cursor_;
                }
                break;

            case State::METHOD:
                if (is_space(c)) {
                    state_ = State::SPACE_BEFORE_URI;
                }
                break;

            case State::SPACE_BEFORE_URI:
                if (!is_space(c)) {
                    const char* uri_start = cursor_ - 1;
                    uri_ = std::string_view(uri_start, 0);
                    state_ = State::URI;
                    // Don't break, continue to URI processing
                }
                // Fall through

            case State::URI:
                if (c == ' ') {
                    state_ = State::HTTP_VERSION_H;
                }
                else {
                    uri_ = std::string_view(uri_.data(), uri_.size() + 1);
                }
                break;

            case State::HTTP_VERSION_H:
                if (c == 'H') state_ = State::HTTP_VERSION_T1;
                break;

            case State::HTTP_VERSION_T1:
                if (c == 'T') state_ = State::HTTP_VERSION_T2;
                break;

            case State::HTTP_VERSION_T2:
                if (c == 'T') state_ = State::HTTP_VERSION_P;
                break;

            case State::HTTP_VERSION_P:
                if (c == 'P') state_ = State::HTTP_VERSION_SLASH;
                break;

            case State::HTTP_VERSION_SLASH:
                if (c == '/') state_ = State::HTTP_VERSION_MAJOR_START;
                break;

            case State::HTTP_VERSION_MAJOR_START:
                if (is_digit(c)) {
                    major_version_ = c - '0';
                    state_ = State::HTTP_VERSION_MAJOR;
                }
                break;

            case State::HTTP_VERSION_MAJOR:
                if (c == '.') {
                    state_ = State::HTTP_VERSION_MINOR_START;
                }
                else if (is_digit(c)) {
                    major_version_ = major_version_ * 10 + (c - '0');
                }
                break;

            case State::HTTP_VERSION_MINOR_START:
                if (is_digit(c)) {
                    minor_version_ = c - '0';
                    state_ = State::HTTP_VERSION_MINOR;
                }
                break;

            case State::HTTP_VERSION_MINOR:
                if (c == '\r') {
                    state_ = State::EXPECTING_NEWLINE_1;
                }
                else if (is_digit(c)) {
                    minor_version_ = minor_version_ * 10 + (c - '0');
                }
                break;

            case State::EXPECTING_NEWLINE_1:
                if (c == '\n') state_ = State::HEADER_LINE_START;
                break;

            case State::HEADER_LINE_START:
                if (c == '\r') {
                    state_ = State::EXPECTING_NEWLINE_2;
                }
                else if (!is_space(c)) {
                    current_header_name_.clear();
                    current_header_name_ += c;
                    state_ = State::HEADER_NAME;
                }
                break;

            case State::HEADER_NAME:
                if (c == ':') {
                    state_ = State::HEADER_VALUE_START;
                }
                else if (is_token_char(c)) {
                    current_header_name_ += c;
                }
                break;

            case State::HEADER_VALUE_START:
                if (!is_space(c)) {
                    // Start of header value
                    const char* value_start = cursor_ - 1;
                    std::string value;
                    state_ = State::HEADER_VALUE;
                    // Continue to process the value
                    --cursor_; // Rewind to process this character in HEADER_VALUE
                }
                break;

            case State::HEADER_VALUE:
                if (c == '\r') {
                    // End of header value
                    const char* value_end = cursor_ - 1;
                    while (value_end > buffer_start_ && is_space(*(value_end - 1))) --value_end;

                    std::string header_value(buffer_start_ + (cursor_ - buffer_start_ - (value_end - (cursor_ - 1))),
                        value_end - (buffer_start_ + (cursor_ - buffer_start_ - (value_end - (cursor_ - 1)))));

                    headers_[current_header_name_] = header_value;

                    // Check for important headers
                    if (current_header_name_ == "Content-Length") {
                        content_length_ = std::stoul(header_value);
                    }
                    else if (current_header_name_ == "Connection") {
                        keep_alive_ = (header_value == "keep-alive" || header_value == "Keep-Alive");
                    }

                    state_ = State::EXPECTING_NEWLINE_1;
                }
                break;

            case State::EXPECTING_NEWLINE_2:
                if (c == '\n') {
                    // End of headers
                    if (content_length_ > 0) {
                        state_ = State::BODY;
                        // Start of body is current position
                        const char* body_start = cursor_;
                        body_ = std::string_view(body_start, 0);
                    }
                    else {
                        state_ = State::COMPLETE;
                        return true;
                    }
                }
                break;

            case State::BODY:
                ++body_bytes_received_;
                body_ = std::string_view(body_.data(), body_.size() + 1);

                if (body_bytes_received_ >= content_length_) {
                    state_ = State::COMPLETE;
                    return true;
                }
                break;

            default:
                break;
            }
        }

        return state_ == State::COMPLETE;
    }

    // Getters
    FORCE_INLINE std::string_view method() const noexcept { return method_; }
    FORCE_INLINE std::string_view uri() const noexcept { return uri_; }
    FORCE_INLINE std::string_view body() const noexcept { return body_; }
    FORCE_INLINE int version() const noexcept { return major_version_ * 10 + minor_version_; }
    FORCE_INLINE bool keep_alive() const noexcept { return keep_alive_; }
    FORCE_INLINE bool complete() const noexcept { return state_ == State::COMPLETE; }
    FORCE_INLINE std::string_view header(const std::string& name) const {
        auto it = headers_.find(name);
        return it != headers_.end() ? std::string_view(it->second) : std::string_view();
    }
    FORCE_INLINE size_t content_length() const noexcept { return content_length_; }
};

// ============================================================================
// MEMORY ARENA
// ============================================================================
class CACHE_ALIGN MemoryArena {
private:
    struct CACHE_ALIGN MemoryBlock {
        void* memory;
        size_t size;
        size_t used;
        MemoryBlock* next;

        MemoryBlock(size_t block_size) : size(block_size), used(0), next(nullptr) {
            if constexpr (USE_HUGE_PAGES) {
                SIZE_T large_page_minimum = GetLargePageMinimum();
                size_t aligned_size = ((block_size + large_page_minimum - 1) / large_page_minimum) * large_page_minimum;
                memory = VirtualAlloc(nullptr, aligned_size,
                    MEM_COMMIT | MEM_RESERVE | MEM_LARGE_PAGES,
                    PAGE_READWRITE);
                if (!memory) {
                    memory = VirtualAlloc(nullptr, block_size,
                        MEM_COMMIT | MEM_RESERVE,
                        PAGE_READWRITE);
                }
            }
            else {
                memory = VirtualAlloc(nullptr, block_size,
                    MEM_COMMIT | MEM_RESERVE,
                    PAGE_READWRITE);
            }
            if (!memory) throw std::bad_alloc();
        }

        ~MemoryBlock() {
            if (memory) VirtualFree(memory, 0, MEM_RELEASE);
        }
    };

    MemoryBlock* current_block_;
    size_t block_size_;
    std::mutex mutex_;

public:
    MemoryArena(size_t initial_size = 64 * 1024 * 1024) : block_size_(initial_size) {
        current_block_ = new MemoryBlock(block_size_);
    }

    ~MemoryArena() {
        while (current_block_) {
            MemoryBlock* next = current_block_->next;
            delete current_block_;
            current_block_ = next;
        }
    }

    void* allocate(size_t size, size_t alignment = 16) {
        std::lock_guard lock(mutex_);

        uintptr_t ptr = reinterpret_cast<uintptr_t>(
            reinterpret_cast<char*>(current_block_->memory) + current_block_->used);
        uintptr_t aligned_ptr = (ptr + alignment - 1) & ~(alignment - 1);
        size_t padding = aligned_ptr - ptr;

        if (current_block_->used + size + padding > current_block_->size) {
            size_t new_block_size = std::max(block_size_, size + alignment);
            MemoryBlock* new_block = new MemoryBlock(new_block_size);
            new_block->next = current_block_;
            current_block_ = new_block;

            ptr = reinterpret_cast<uintptr_t>(current_block_->memory);
            aligned_ptr = (ptr + alignment - 1) & ~(alignment - 1);
            padding = aligned_ptr - ptr;
        }

        void* result = reinterpret_cast<void*>(aligned_ptr);
        current_block_->used = (aligned_ptr - reinterpret_cast<uintptr_t>(current_block_->memory)) + size;
        return result;
    }

    void deallocate(void* ptr) noexcept {
        // Arena doesn't support individual deallocation
    }

    template<typename T, typename... Args>
    T* construct(Args&&... args) {
        void* mem = allocate(sizeof(T), alignof(T));
        return new (mem) T(std::forward<Args>(args)...);
    }

    void reset() noexcept {
        std::lock_guard lock(mutex_);
        for (MemoryBlock* block = current_block_; block; block = block->next) {
            block->used = 0;
        }
    }
};

// ============================================================================
// CONNECTION SLOT (WITH PARSER FIXED)
// ============================================================================
struct CACHE_ALIGN ConnectionSlot {
    SOCKET socket;
    WSAOVERLAPPED overlapped;
    char buffer[BUFFER_SIZE];
    HttpParser parser;  // FIXED: Proper parser member
    std::atomic<bool> in_use{ false };
    ConnectionSlot* next{ nullptr };
    uint64_t last_used{ 0 };

    ConnectionSlot() : socket(INVALID_SOCKET) {
        memset(&overlapped, 0, sizeof(WSAOVERLAPPED));
        memset(buffer, 0, BUFFER_SIZE);
    }

    void reset() noexcept {
        socket = INVALID_SOCKET;
        memset(&overlapped, 0, sizeof(WSAOVERLAPPED));
        parser.reset();
        in_use.store(false, std::memory_order_relaxed);
        last_used = 0;
    }
};

// ============================================================================
// CONNECTION POOL
// ============================================================================
class CACHE_ALIGN ConnectionPool {
private:
    ConnectionSlot* free_list_;
    std::mutex mutex_;
    MemoryArena& arena_;
    std::atomic<size_t> allocated_{ 0 };
    std::atomic<size_t> in_use_{ 0 };

public:
    explicit ConnectionPool(MemoryArena& arena) noexcept : arena_(arena), free_list_(nullptr) {}

    ConnectionSlot* acquire() noexcept {
        ConnectionSlot* slot = free_list_;
        while (slot) {
            bool expected = false;
            if (slot->in_use.compare_exchange_weak(expected, true)) {
                in_use_.fetch_add(1, std::memory_order_relaxed);
                return slot;
            }
            slot = slot->next;
        }

        return allocate_new();
    }

    NO_INLINE ConnectionSlot* allocate_new() noexcept {
        std::lock_guard lock(mutex_);

        ConnectionSlot* new_slot = arena_.construct<ConnectionSlot>();
        new_slot->in_use.store(true, std::memory_order_release);
        new_slot->next = free_list_;
        free_list_ = new_slot;

        allocated_.fetch_add(1, std::memory_order_relaxed);
        in_use_.fetch_add(1, std::memory_order_relaxed);

        return new_slot;
    }

    void release(ConnectionSlot* slot) noexcept {
        slot->reset();
        slot->in_use.store(false, std::memory_order_release);
        in_use_.fetch_sub(1, std::memory_order_relaxed);
    }

    size_t allocated() const noexcept { return allocated_.load(std::memory_order_relaxed); }
    size_t in_use() const noexcept { return in_use_.load(std::memory_order_relaxed); }
};

// ============================================================================
// ROUTER
// ============================================================================
class CACHE_ALIGN Router {
private:
    struct RouteNode {
        std::string_view segment;
        bool is_param{ false };
        bool is_wildcard{ false };
        std::unordered_map<std::string_view, RouteNode*> children;
        std::function<void(std::string_view, std::string_view)> handler;
    };

    RouteNode* root_;
    MemoryArena& arena_;

    static std::vector<std::string_view> split_path(std::string_view path) {
        std::vector<std::string_view> parts;
        size_t start = 0;
        while (start < path.size()) {
            if (path[start] == '/') {
                ++start;
                continue;
            }
            size_t end = path.find('/', start);
            if (end == std::string_view::npos) {
                parts.push_back(path.substr(start));
                break;
            }
            parts.push_back(path.substr(start, end - start));
            start = end + 1;
        }
        return parts;
    }

public:
    Router(MemoryArena& arena) : arena_(arena) {
        root_ = arena_.construct<RouteNode>();
    }

    void add_route(std::string_view method, std::string_view path,
        std::function<void(std::string_view, std::string_view)> handler) {
        auto parts = split_path(path);
        RouteNode* current = root_;

        for (auto part : parts) {
            if (part.empty()) continue;

            if (part[0] == ':') {
                if (!current->children.count(":param")) {
                    RouteNode* param_node = arena_.construct<RouteNode>();
                    param_node->is_param = true;
                    param_node->segment = part.substr(1);
                    current->children[":param"] = param_node;
                }
                current = current->children[":param"];
            }
            else if (part == "*") {
                if (!current->children.count("*")) {
                    RouteNode* wildcard_node = arena_.construct<RouteNode>();
                    wildcard_node->is_wildcard = true;
                    current->children["*"] = wildcard_node;
                }
                current = current->children["*"];
                break;
            }
            else {
                if (!current->children.count(part)) {
                    current->children[part] = arena_.construct<RouteNode>();
                }
                current = current->children[part];
            }
        }

        current->handler = std::move(handler);
    }

    std::pair<std::function<void(std::string_view, std::string_view)>, std::string_view>
        find_route(std::string_view method, std::string_view path) const {
        auto parts = split_path(path);
        RouteNode* current = root_;
        std::string_view param_value;

        for (auto part : parts) {
            if (part.empty()) continue;

            auto it = current->children.find(part);
            if (it != current->children.end()) {
                current = it->second;
            }
            else if (current->children.count(":param")) {
                current = current->children.at(":param");
                param_value = part;
            }
            else if (current->children.count("*")) {
                current = current->children.at("*");
                break;
            }
            else {
                return { nullptr, "" };
            }
        }

        return { current->handler, param_value };
    }

    void get(std::string_view path, std::function<void(std::string_view, std::string_view)> handler) {
        add_route("GET", path, std::move(handler));
    }

    void post(std::string_view path, std::function<void(std::string_view, std::string_view)> handler) {
        add_route("POST", path, std::move(handler));
    }

    void put(std::string_view path, std::function<void(std::string_view, std::string_view)> handler) {
        add_route("PUT", path, std::move(handler));
    }

    void del(std::string_view path, std::function<void(std::string_view, std::string_view)> handler) {
        add_route("DELETE", path, std::move(handler));
    }
};

// ============================================================================
// RESPONSE CACHE
// ============================================================================
class CACHE_ALIGN ResponseCache {
private:
    struct CacheEntry {
        uint64_t key;
        std::string response;
        std::chrono::steady_clock::time_point timestamp;
        CacheEntry* prev{ nullptr };
        CacheEntry* next{ nullptr };
    };

    static constexpr size_t SHARD_COUNT = 64;
    struct CacheShard {
        std::shared_mutex mutex;
        std::unordered_map<uint64_t, CacheEntry*> entries;
        CacheEntry* head{ nullptr };
        CacheEntry* tail{ nullptr };
        size_t size{ 0 };
        size_t capacity;

        CacheShard(size_t cap) : capacity(cap) {}
    };

    std::vector<CacheShard*> shards_;
    MemoryArena& arena_;

    uint64_t hash_key(std::string_view method, std::string_view path) const {
        uint64_t hash = 14695981039346656037ULL;
        for (char c : method) {
            hash ^= static_cast<uint64_t>(c);
            hash *= 1099511628211ULL;
        }
        for (char c : path) {
            hash ^= static_cast<uint64_t>(c);
            hash *= 1099511628211ULL;
        }
        return hash;
    }

    size_t get_shard_index(uint64_t key) const {
        return key % SHARD_COUNT;
    }

public:
    ResponseCache(MemoryArena& arena, size_t capacity) : arena_(arena) {
        size_t shard_capacity = capacity / SHARD_COUNT;
        for (size_t i = 0; i < SHARD_COUNT; ++i) {
            shards_.push_back(arena_.construct<CacheShard>(shard_capacity));
        }
    }

    std::string* get(std::string_view method, std::string_view path) {
        uint64_t key = hash_key(method, path);
        size_t shard_idx = get_shard_index(key);
        auto& shard = *shards_[shard_idx];

        std::shared_lock lock(shard.mutex);
        auto it = shard.entries.find(key);
        if (it != shard.entries.end()) {
            CacheEntry* entry = it->second;
            entry->timestamp = std::chrono::steady_clock::now();
            return &entry->response;
        }
        return nullptr;
    }

    void put(std::string_view method, std::string_view path, std::string response) {
        uint64_t key = hash_key(method, path);
        size_t shard_idx = get_shard_index(key);
        auto& shard = *shards_[shard_idx];

        std::unique_lock lock(shard.mutex);

        auto it = shard.entries.find(key);
        if (it != shard.entries.end()) {
            it->second->response = std::move(response);
            it->second->timestamp = std::chrono::steady_clock::now();
            return;
        }

        if (shard.size >= shard.capacity && shard.tail) {
            CacheEntry* to_evict = shard.tail;
            shard.tail = to_evict->prev;
            if (shard.tail) shard.tail->next = nullptr;
            if (to_evict == shard.head) shard.head = nullptr;

            shard.entries.erase(to_evict->key);
            --shard.size;
        }

        CacheEntry* entry = arena_.construct<CacheEntry>();
        entry->key = key;
        entry->response = std::move(response);
        entry->timestamp = std::chrono::steady_clock::now();

        entry->prev = nullptr;
        entry->next = shard.head;
        if (shard.head) shard.head->prev = entry;
        shard.head = entry;
        if (!shard.tail) shard.tail = entry;

        shard.entries[key] = entry;
        ++shard.size;
    }
};

// ============================================================================
// BEASTWEB SERVER (FIXED)
// ============================================================================
class BeastWebServer {
private:
    struct WorkerThread {
        HANDLE iocp_handle;
        std::atomic<bool> running{ true };
        std::thread thread;
        size_t thread_id;
        std::atomic<uint64_t> requests_processed{ 0 };
        std::atomic<uint64_t> bytes_sent{ 0 };
        std::atomic<uint64_t> bytes_received{ 0 };
        ConnectionPool* conn_pool;
        Router* router;
        ResponseCache* cache;
    };

    struct AcceptContext {
        OVERLAPPED overlapped;
        SOCKET accept_socket;
        char buffer[2 * (sizeof(sockaddr_in) + 16)];

        AcceptContext() {
            memset(&overlapped, 0, sizeof(OVERLAPPED));
            accept_socket = INVALID_SOCKET;
        }

        ~AcceptContext() {
            if (accept_socket != INVALID_SOCKET) {
                closesocket(accept_socket);
            }
        }
    };

    std::string listen_address_;
    unsigned short listen_port_;
    size_t num_workers_;

    SOCKET listen_socket_;
    HANDLE iocp_handle_;
    std::vector<WorkerThread*> workers_;
    std::unique_ptr<MemoryArena> arena_;
    std::unique_ptr<ConnectionPool> conn_pool_;
    std::unique_ptr<Router> router_;
    std::unique_ptr<ResponseCache> cache_;

    LPFN_ACCEPTEX acceptex_;
    LPFN_GETACCEPTEXSOCKADDRS get_acceptex_sockaddrs_;

    std::atomic<bool> running_{ false };
    std::thread stats_thread_;

    void initialize_winsock() {
        WSADATA wsaData;
        if (WSAStartup(MAKEWORD(2, 2), &wsaData) != 0) {
            throw std::runtime_error("WSAStartup failed");
        }

        listen_socket_ = WSASocket(AF_INET, SOCK_STREAM, IPPROTO_TCP, nullptr, 0, WSA_FLAG_OVERLAPPED);
        if (listen_socket_ == INVALID_SOCKET) {
            WSACleanup();
            throw std::runtime_error("WSASocket failed");
        }

        int optval = 1;
        setsockopt(listen_socket_, SOL_SOCKET, SO_REUSEADDR,
            reinterpret_cast<const char*>(&optval), sizeof(optval));
        setsockopt(listen_socket_, IPPROTO_TCP, TCP_NODELAY,
            reinterpret_cast<const char*>(&optval), sizeof(optval));

        sockaddr_in addr{};
        addr.sin_family = AF_INET;
        addr.sin_addr.s_addr = inet_addr(listen_address_.c_str());
        addr.sin_port = htons(listen_port_);

        if (bind(listen_socket_, reinterpret_cast<sockaddr*>(&addr), sizeof(addr)) == SOCKET_ERROR) {
            closesocket(listen_socket_);
            WSACleanup();
            throw std::runtime_error("bind failed");
        }

        if (listen(listen_socket_, SOMAXCONN) == SOCKET_ERROR) {
            closesocket(listen_socket_);
            WSACleanup();
            throw std::runtime_error("listen failed");
        }

        iocp_handle_ = CreateIoCompletionPort(INVALID_HANDLE_VALUE, nullptr, 0, 0);
        if (!iocp_handle_) {
            closesocket(listen_socket_);
            WSACleanup();
            throw std::runtime_error("CreateIoCompletionPort failed");
        }

        if (!CreateIoCompletionPort(reinterpret_cast<HANDLE>(listen_socket_),
            iocp_handle_, 0, 0)) {
            CloseHandle(iocp_handle_);
            closesocket(listen_socket_);
            WSACleanup();
            throw std::runtime_error("Failed to associate socket with IOCP");
        }

        GUID acceptex_guid = WSAID_ACCEPTEX;
        DWORD bytes;
        SOCKET temp_socket = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);

        if (WSAIoctl(temp_socket, SIO_GET_EXTENSION_FUNCTION_POINTER,
            &acceptex_guid, sizeof(acceptex_guid),
            &acceptex_, sizeof(acceptex_),
            &bytes, nullptr, nullptr) != 0) {
            closesocket(temp_socket);
            throw std::runtime_error("Failed to load AcceptEx");
        }

        GUID getacceptexsockaddrs_guid = WSAID_GETACCEPTEXSOCKADDRS;
        if (WSAIoctl(temp_socket, SIO_GET_EXTENSION_FUNCTION_POINTER,
            &getacceptexsockaddrs_guid, sizeof(getacceptexsockaddrs_guid),
            &get_acceptex_sockaddrs_, sizeof(get_acceptex_sockaddrs_),
            &bytes, nullptr, nullptr) != 0) {
            closesocket(temp_socket);
            throw std::runtime_error("Failed to load GetAcceptExSockaddrs");
        }

        closesocket(temp_socket);
    }

    void post_accept() {
        AcceptContext* ctx = new AcceptContext();
        ctx->accept_socket = WSASocket(AF_INET, SOCK_STREAM, IPPROTO_TCP, nullptr, 0, WSA_FLAG_OVERLAPPED);

        if (ctx->accept_socket == INVALID_SOCKET) {
            delete ctx;
            return;
        }

        DWORD bytes_received = 0;
        BOOL result = acceptex_(listen_socket_, ctx->accept_socket, ctx->buffer, 0,
            sizeof(sockaddr_in) + 16, sizeof(sockaddr_in) + 16,
            &bytes_received, &ctx->overlapped);

        if (!result && WSAGetLastError() != ERROR_IO_PENDING) {
            delete ctx;
        }
    }

    static DWORD WINAPI worker_thread_proc(LPVOID param) {
        WorkerThread* ctx = static_cast<WorkerThread*>(param);

        SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_HIGHEST);

        while (ctx->running.load(std::memory_order_acquire)) {
            DWORD bytes_transferred = 0;
            ULONG_PTR completion_key = 0;
            OVERLAPPED* overlapped = nullptr;

            BOOL result = GetQueuedCompletionStatus(ctx->iocp_handle,
                &bytes_transferred,
                &completion_key,
                &overlapped,
                INFINITE);

            if (!result) {
                DWORD error = GetLastError();
                if (error == WAIT_TIMEOUT) continue;
                if (error == ERROR_ABANDONED_WAIT_0) break;
                continue;
            }

            if (bytes_transferred == 0 && completion_key == 0) {
                break;
            }

            ctx->requests_processed++;
        }

        return 0;
    }

    void start_reading(WorkerThread* ctx, ConnectionSlot* conn_slot) {
        WSABUF wsabuf;
        wsabuf.buf = conn_slot->buffer;
        wsabuf.len = BUFFER_SIZE;

        DWORD flags = 0;
        DWORD bytes_received = 0;

        memset(&conn_slot->overlapped, 0, sizeof(WSAOVERLAPPED));

        int result = WSARecv(conn_slot->socket, &wsabuf, 1,
            &bytes_received, &flags,
            &conn_slot->overlapped, nullptr);

        if (result == SOCKET_ERROR && WSAGetLastError() != WSA_IO_PENDING) {
            ctx->conn_pool->release(conn_slot);
        }
    }

    void process_request(WorkerThread* ctx, ConnectionSlot* conn_slot) {
        auto& parser = conn_slot->parser;  // FIXED: Direct access to parser

        std::string* cached_response = cache_->get(parser.method(), parser.uri());
        if (cached_response) {
            send_response(ctx, conn_slot, *cached_response);
            ctx->requests_processed.fetch_add(1, std::memory_order_relaxed);
            return;
        }

        auto [handler, param] = router_->find_route(parser.method(), parser.uri());

        if (handler) {
            handler(param, parser.body());

            std::string response = generate_response(parser.method(), parser.uri(), param);

            if (parser.method() == "GET") {
                cache_->put(parser.method(), parser.uri(), response);
            }

            send_response(ctx, conn_slot, response);
            ctx->requests_processed.fetch_add(1, std::memory_order_relaxed);
        }
        else {
            send_response(ctx, conn_slot,
                "HTTP/1.1 404 Not Found\r\n"
                "Content-Type: text/plain\r\n"
                "Content-Length: 13\r\n"
                "Connection: keep-alive\r\n"
                "\r\n"
                "404 Not Found");
            ctx->requests_processed.fetch_add(1, std::memory_order_relaxed);
        }
    }

    static std::string generate_response(std::string_view method,
        std::string_view uri,
        std::string_view param) {
        std::string response = "HTTP/1.1 200 OK\r\n"
            "Content-Type: application/json\r\n"
            "Content-Length: ";

        std::string json = "{\"status\":\"ok\",\"path\":\"" + std::string(uri) +
            "\",\"method\":\"" + std::string(method) + "\"";

        if (!param.empty()) {
            json += ",\"param\":\"" + std::string(param) + "\"";
        }
        json += "}";

        response.append(std::to_string(json.size()));
        response.append("\r\n\r\n");
        response.append(json);

        return response;
    }

    void send_response(WorkerThread* ctx, ConnectionSlot* conn_slot, const std::string& response) {
        WSABUF wsabuf;
        wsabuf.buf = const_cast<char*>(response.data());
        wsabuf.len = static_cast<ULONG>(response.size());

        DWORD bytes_sent = 0;
        memset(&conn_slot->overlapped, 0, sizeof(WSAOVERLAPPED));

        int result = WSASend(conn_slot->socket, &wsabuf, 1,
            &bytes_sent, 0,
            &conn_slot->overlapped, nullptr);

        if (result == SOCKET_ERROR && WSAGetLastError() != WSA_IO_PENDING) {
            ctx->conn_pool->release(conn_slot);
        }
        else {
            ctx->bytes_sent.fetch_add(bytes_sent, std::memory_order_relaxed);

            if (conn_slot->parser.keep_alive()) {
                conn_slot->parser.reset();
                start_reading(ctx, conn_slot);
            }
            else {
                ctx->conn_pool->release(conn_slot);
            }
        }
    }

    void stats_reporter() {
        uint64_t last_total_requests = 0;
        auto last_time = std::chrono::steady_clock::now();

        while (running_.load(std::memory_order_acquire)) {
            std::this_thread::sleep_for(std::chrono::seconds(1));

            uint64_t current_requests = 0;
            uint64_t current_sent = 0;
            uint64_t current_received = 0;

            for (const auto& worker : workers_) {
                current_requests += worker->requests_processed.load(std::memory_order_relaxed);
                current_sent += worker->bytes_sent.load(std::memory_order_relaxed);
                current_received += worker->bytes_received.load(std::memory_order_relaxed);
            }

            auto current_time = std::chrono::steady_clock::now();
            double elapsed = std::chrono::duration<double>(current_time - last_time).count();
            double rps = (current_requests - last_total_requests) / elapsed;

            PROCESS_MEMORY_COUNTERS_EX pmc;
            GetProcessMemoryInfo(GetCurrentProcess(),
                reinterpret_cast<PROCESS_MEMORY_COUNTERS*>(&pmc),
                sizeof(pmc));

            std::cout << "\r"
                << "RPS: " << std::setw(8) << static_cast<int>(rps) << " | "
                << "Reqs: " << std::setw(12) << current_requests << " | "
                << "Conn: " << std::setw(8) << conn_pool_->in_use() << " | "
                << "Mem: " << std::setw(6) << (pmc.WorkingSetSize / 1024 / 1024) << "MB"
                << std::flush;

            last_total_requests = current_requests;
            last_time = current_time;
        }
    }

public:
    BeastWebServer(const std::string& address = "0.0.0.0",
        unsigned short port = 8080,
        size_t threads = std::thread::hardware_concurrency())
        : listen_address_(address), listen_port_(port), num_workers_(threads) {

        SetPriorityClass(GetCurrentProcess(), HIGH_PRIORITY_CLASS);
        SetThreadExecutionState(ES_CONTINUOUS | ES_SYSTEM_REQUIRED | ES_AWAYMODE_REQUIRED);

        arena_ = std::make_unique<MemoryArena>(256 * 1024 * 1024);
        conn_pool_ = std::make_unique<ConnectionPool>(*arena_);
        router_ = std::make_unique<Router>(*arena_);
        cache_ = std::make_unique<ResponseCache>(*arena_, RESPONSE_CACHE_ENTRIES);

        initialize_winsock();

        router_->get("/health", [](std::string_view param, std::string_view body) {});
        router_->get("/api/v1/users/:id", [](std::string_view id, std::string_view body) {});
        router_->post("/api/v1/users", [](std::string_view param, std::string_view body) {});
        router_->get("/api/v1/products", [](std::string_view param, std::string_view body) {});
    }

    ~BeastWebServer() {
        stop();
    }

    void start() {
        if (running_.exchange(true)) return;

        std::cout << "=============================================\n";
        std::cout << "🔥 BEASTWEB ULTIMATE v6.0 🔥\n";
        std::cout << "=============================================\n";
        std::cout << "Address: " << listen_address_ << ":" << listen_port_ << "\n";
        std::cout << "Worker Threads: " << num_workers_ << "\n";
        std::cout << "Max Connections: " << MAX_CONCURRENT_CONNECTIONS << "\n";
        std::cout << "Huge Pages: " << (USE_HUGE_PAGES ? "ENABLED" : "DISABLED") << "\n";
        std::cout << "=============================================\n\n";

        workers_.reserve(num_workers_);
        for (size_t i = 0; i < num_workers_; ++i) {
            WorkerThread* worker = new WorkerThread();
            worker->iocp_handle = iocp_handle_;
            worker->thread_id = i;
            worker->running = true;
            worker->conn_pool = conn_pool_.get();
            worker->router = router_.get();
            worker->cache = cache_.get();

            worker->thread = std::thread(worker_thread_proc, worker);
            workers_.push_back(worker);

            SetThreadAffinityMask(worker->thread.native_handle(), 1ULL << (i % 64));
        }

        for (int i = 0; i < 100; ++i) {
            post_accept();
        }

        stats_thread_ = std::thread(&BeastWebServer::stats_reporter, this);

        std::cout << "Server is RUNNING! Press Enter to stop.\n";
        std::cin.get();

        stop();
    }

    void stop() {
        if (!running_.exchange(false)) return;

        for (size_t i = 0; i < workers_.size(); ++i) {
            PostQueuedCompletionStatus(iocp_handle_, 0, 0, nullptr);
        }

        for (auto& worker : workers_) {
            worker->running = false;
            if (worker->thread.joinable()) {
                worker->thread.join();
            }
            delete worker;
        }

        if (stats_thread_.joinable()) {
            stats_thread_.join();
        }

        if (listen_socket_ != INVALID_SOCKET) {
            closesocket(listen_socket_);
        }

        if (iocp_handle_) {
            CloseHandle(iocp_handle_);
        }

        WSACleanup();
    }

    void get(std::string_view path, std::function<void(std::string_view, std::string_view)> handler) {
        router_->get(path, std::move(handler));
    }

    void post(std::string_view path, std::function<void(std::string_view, std::string_view)> handler) {
        router_->post(path, std::move(handler));
    }

    void put(std::string_view path, std::function<void(std::string_view, std::string_view)> handler) {
        router_->put(path, std::move(handler));
    }

    void del(std::string_view path, std::function<void(std::string_view, std::string_view)> handler) {
        router_->del(path, std::move(handler));
    }
};

// ============================================================================
// MAIN FUNCTION
// ============================================================================
int main(int argc, char* argv[]) {
    try {
        std::string address = "0.0.0.0";
        unsigned short port = 8080;
        size_t threads = std::thread::hardware_concurrency();

        if (argc > 1) address = argv[1];
        if (argc > 2) port = static_cast<unsigned short>(std::atoi(argv[2]));
        if (argc > 3) threads = static_cast<size_t>(std::atoi(argv[3]));

        BeastWebServer server(address, port, threads);
        server.start();

    }
    catch (const std::exception& e) {
        std::cerr << "FATAL ERROR: " << e.what() << std::endl;
        return 1;
    }

    return 0;
}