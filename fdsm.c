int fdsm_init(int n, int C, double alpha, int max_operations, const int *parents, const int *colors);
int fdsm_update(int v, int color);
int fdsm_query(int v, int *color, int *frequency);
void fdsm_destroy(void);
int fdsm_move(int v, int parent);
int fdsm_add_leaf(int parent, int color);
int fdsm_remove_leaf(int v);

static int api_ready;
#ifndef DSM_FC_AHLT_BACKEND_H
#define DSM_FC_AHLT_BACKEND_H

static void dsm_fc_ahlt_init(int capacity, int ncolors, int current_n,
                      const int *parent, const unsigned char *is_alive);
static int dsm_fc_ahlt_is_dynamic(void);

static void dsm_fc_ahlt_clear_marks(void);
static void dsm_fc_ahlt_mark(int v, int c, int pool_node);
static int dsm_fc_ahlt_topmarked(int v, int c);

static int dsm_fc_ahlt_color_leaf_size(int c);
static int dsm_fc_ahlt_color_leaf_prev(int c, int v);
static int dsm_fc_ahlt_color_leaf_next(int c, int v);
static int dsm_fc_ahlt_color_leaf_count_subtree(int c, int v);
static int dsm_fc_ahlt_color_leaf_first_subtree(int c, int v);
static int dsm_fc_ahlt_color_leaf_last_subtree(int c, int v);
static void dsm_fc_ahlt_mark_color_leaf(int v, int c);
static void dsm_fc_ahlt_unmark_color_leaf(int v, int c);
static int dsm_fc_ahlt_nearest_change_ancestor(int v, int c);
static int dsm_fc_ahlt_prepare_subtree_move_color(int v, int new_parent, int c,
                                           int *cnt, int *total, int *top,
                                           int *first_leaf, int *last_leaf,
                                           int *old_anchor,
                                           int *new_anchor);

static int dsm_fc_ahlt_add_leaf(int parent, int leaf);
static int dsm_fc_ahlt_delete_leaf(int leaf);

static int dsm_fc_ahlt_link_subtree(int v, int new_parent);

#endif

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct AVLNode {
    int left;
    int right;
    int height;
    int next_free;
    int payload;
    int64_t key;
} AVLNode;

typedef struct AVLPool {
    AVLNode *node;
    int capacity;
    int next;
    int free_head;
    int root;
} AVLPool;

static AVLPool mark_pool;
static AVLPool leaf_pool;
static int fc_capacity;
static int fc_ncolors;
static int *fc_parent;
static unsigned char *fc_active;
static int *fc_leaf_color;
static int *fc_leaf_count;

static int avl_height(const AVLPool *pool, int x) {
    return x ? pool->node[x].height : 0;
}

static int avl_max(int a, int b) { return a > b ? a : b; }

static void avl_pull(AVLPool *pool, int x) {
    pool->node[x].height = 1 + avl_max(avl_height(pool, pool->node[x].left),
                                       avl_height(pool, pool->node[x].right));
}

static int avl_rotate_left(AVLPool *pool, int x) {
    int y = pool->node[x].right;
    pool->node[x].right = pool->node[y].left;
    pool->node[y].left = x;
    avl_pull(pool, x);
    avl_pull(pool, y);
    return y;
}

static int avl_rotate_right(AVLPool *pool, int x) {
    int y = pool->node[x].left;
    pool->node[x].left = pool->node[y].right;
    pool->node[y].right = x;
    avl_pull(pool, x);
    avl_pull(pool, y);
    return y;
}

static int avl_balance(AVLPool *pool, int x) {
    int balance;
    if (!x) return 0;
    avl_pull(pool, x);
    balance = avl_height(pool, pool->node[x].left) -
              avl_height(pool, pool->node[x].right);
    if (balance > 1) {
        int left = pool->node[x].left;
        if (avl_height(pool, pool->node[left].right) >
            avl_height(pool, pool->node[left].left)) {
            pool->node[x].left = avl_rotate_left(pool, left);
        }
        return avl_rotate_right(pool, x);
    }
    if (balance < -1) {
        int right = pool->node[x].right;
        if (avl_height(pool, pool->node[right].left) >
            avl_height(pool, pool->node[right].right)) {
            pool->node[x].right = avl_rotate_right(pool, right);
        }
        return avl_rotate_left(pool, x);
    }
    return x;
}

static int avl_alloc(AVLPool *pool, int64_t key, int payload) {
    int x;
    if (pool->free_head) {
        x = pool->free_head;
        pool->free_head = pool->node[x].next_free;
    } else {
        if (pool->next >= pool->capacity) {
            fprintf(stderr, "AVL capacity exhausted\n");
            abort();
        }
        x = pool->next++;
    }
    memset(&pool->node[x], 0, sizeof(pool->node[x]));
    pool->node[x].height = 1;
    pool->node[x].key = key;
    pool->node[x].payload = payload;
    return x;
}

static void avl_recycle(AVLPool *pool, int x) {
    pool->node[x].next_free = pool->free_head;
    pool->free_head = x;
}

static int avl_insert_rec(AVLPool *pool, int root, int64_t key, int payload) {
    if (!root) return avl_alloc(pool, key, payload);
    if (key < pool->node[root].key) {
        pool->node[root].left = avl_insert_rec(pool, pool->node[root].left,
                                               key, payload);
    } else if (key > pool->node[root].key) {
        pool->node[root].right = avl_insert_rec(pool, pool->node[root].right,
                                                key, payload);
    } else {
        pool->node[root].payload = payload;
        return root;
    }
    return avl_balance(pool, root);
}

static int avl_delete_rec(AVLPool *pool, int root, int64_t key) {
    int child;
    if (!root) return 0;
    if (key < pool->node[root].key) {
        pool->node[root].left = avl_delete_rec(pool, pool->node[root].left, key);
    } else if (key > pool->node[root].key) {
        pool->node[root].right = avl_delete_rec(pool, pool->node[root].right, key);
    } else if (!pool->node[root].left || !pool->node[root].right) {
        child = pool->node[root].left ? pool->node[root].left : pool->node[root].right;
        avl_recycle(pool, root);
        return child;
    } else {
        int successor = pool->node[root].right;
        while (pool->node[successor].left) successor = pool->node[successor].left;
        pool->node[root].key = pool->node[successor].key;
        pool->node[root].payload = pool->node[successor].payload;
        pool->node[root].right = avl_delete_rec(pool, pool->node[root].right,
                                                pool->node[successor].key);
    }
    return avl_balance(pool, root);
}

static int avl_find(const AVLPool *pool, int64_t key) {
    int x = pool->root;
    while (x) {
        if (key == pool->node[x].key) return x;
        x = key < pool->node[x].key ? pool->node[x].left : pool->node[x].right;
    }
    return 0;
}

static int avl_lower_bound(const AVLPool *pool, int64_t key) {
    int x = pool->root;
    int answer = 0;
    while (x) {
        if (pool->node[x].key >= key) {
            answer = x;
            x = pool->node[x].left;
        } else {
            x = pool->node[x].right;
        }
    }
    return answer;
}

static int avl_predecessor(const AVLPool *pool, int64_t key) {
    int x = pool->root;
    int answer = 0;
    while (x) {
        if (pool->node[x].key < key) {
            answer = x;
            x = pool->node[x].right;
        } else {
            x = pool->node[x].left;
        }
    }
    return answer;
}

static int64_t fc_key(int c, int v) {
    return (int64_t)c * (int64_t)fc_capacity + v;
}

static int key_color(int64_t key) { return (int)(key / fc_capacity); }
static int key_vertex(int64_t key) { return (int)(key % fc_capacity); }

static void pool_reset(AVLPool *pool) {
    pool->next = 1;
    pool->free_head = 0;
    pool->root = 0;
}

static void dsm_fc_ahlt_init(int capacity, int ncolors, int current_n,
                      const int *parent, const unsigned char *is_alive) {
    int v;
    int avl_capacity = 8 * capacity + 16;
    free(mark_pool.node);
    free(leaf_pool.node);
    free(fc_parent);
    free(fc_active);
    free(fc_leaf_color);
    free(fc_leaf_count);
    memset(&mark_pool, 0, sizeof(mark_pool));
    memset(&leaf_pool, 0, sizeof(leaf_pool));
    fc_capacity = capacity;
    fc_ncolors = ncolors;
    mark_pool.capacity = avl_capacity;
    leaf_pool.capacity = avl_capacity;
    mark_pool.node = (AVLNode *)calloc((size_t)avl_capacity, sizeof(AVLNode));
    leaf_pool.node = (AVLNode *)calloc((size_t)avl_capacity, sizeof(AVLNode));
    fc_parent = (int *)malloc((size_t)capacity * sizeof(int));
    fc_active = (unsigned char *)calloc((size_t)capacity, 1);
    fc_leaf_color = (int *)malloc((size_t)capacity * sizeof(int));
    fc_leaf_count = (int *)calloc((size_t)ncolors, sizeof(int));
    if (!mark_pool.node || !leaf_pool.node || !fc_parent || !fc_active ||
        !fc_leaf_color || !fc_leaf_count) abort();
    pool_reset(&mark_pool);
    pool_reset(&leaf_pool);
    for (v = 0; v < capacity; v++) {
        fc_parent[v] = -1;
        fc_leaf_color[v] = -1;
    }
    for (v = 0; v < current_n; v++) {
        fc_active[v] = is_alive ? is_alive[v] : 1;
        fc_parent[v] = v == 0 ? -1 : parent[v];
    }
}

static int dsm_fc_ahlt_is_dynamic(void) { return 1; }

static void dsm_fc_ahlt_clear_marks(void) {
    pool_reset(&mark_pool);
    pool_reset(&leaf_pool);
    memset(fc_leaf_count, 0, (size_t)fc_ncolors * sizeof(int));
    memset(fc_leaf_color, -1, (size_t)fc_capacity * sizeof(int));
}

static void dsm_fc_ahlt_mark(int v, int c, int pool_node) {
    mark_pool.root = avl_insert_rec(&mark_pool, mark_pool.root, fc_key(c, v), pool_node);
}

static int dsm_fc_ahlt_topmarked(int v, int c) {
    int x = avl_find(&mark_pool, fc_key(c, v));
    if (!x) x = avl_lower_bound(&mark_pool, fc_key(c, v));
    return x && key_color(mark_pool.node[x].key) == c ? mark_pool.node[x].payload : 0;
}

static int dsm_fc_ahlt_color_leaf_size(int c) { return fc_leaf_count[c]; }

static int dsm_fc_ahlt_color_leaf_prev(int c, int v) {
    int x = avl_predecessor(&leaf_pool, fc_key(c, v));
    return x && key_color(leaf_pool.node[x].key) == c ? key_vertex(leaf_pool.node[x].key) : -1;
}

static int dsm_fc_ahlt_color_leaf_next(int c, int v) {
    int x = avl_lower_bound(&leaf_pool, fc_key(c, v + 1));
    return x && key_color(leaf_pool.node[x].key) == c ? key_vertex(leaf_pool.node[x].key) : -1;
}

static int dsm_fc_ahlt_color_leaf_count_subtree(int c, int v) {
    return avl_find(&leaf_pool, fc_key(c, v)) ? 1 : 0;
}

static int dsm_fc_ahlt_color_leaf_first_subtree(int c, int v) {
    int exact = avl_find(&leaf_pool, fc_key(c, v));
    if (exact) return v;
    return dsm_fc_ahlt_color_leaf_next(c, v - 1);
}

static int dsm_fc_ahlt_color_leaf_last_subtree(int c, int v) {
    int exact = avl_find(&leaf_pool, fc_key(c, v));
    if (exact) return v;
    return dsm_fc_ahlt_color_leaf_prev(c, fc_capacity);
}

static void dsm_fc_ahlt_mark_color_leaf(int v, int c) {
    int old = fc_leaf_color[v];
    if (old == c) return;
    if (old >= 0) {
        leaf_pool.root = avl_delete_rec(&leaf_pool, leaf_pool.root, fc_key(old, v));
        fc_leaf_count[old]--;
    }
    fc_leaf_color[v] = c;
    fc_leaf_count[c]++;
    leaf_pool.root = avl_insert_rec(&leaf_pool, leaf_pool.root, fc_key(c, v), v);
}

static void dsm_fc_ahlt_unmark_color_leaf(int v, int c) {
    if (fc_leaf_color[v] == c) {
        fc_leaf_color[v] = -1;
        fc_leaf_count[c]--;
    }
    leaf_pool.root = avl_delete_rec(&leaf_pool, leaf_pool.root, fc_key(c, v));
}

static int dsm_fc_ahlt_nearest_change_ancestor(int v, int c) {
    int x = avl_find(&mark_pool, fc_key(c, v));
    return x ? v : -1;
}

static int dsm_fc_ahlt_prepare_subtree_move_color(int v, int new_parent, int c,
                                           int *cnt, int *total, int *top,
                                           int *first_leaf, int *last_leaf,
                                           int *old_anchor, int *new_anchor) {
    int first = dsm_fc_ahlt_color_leaf_first_subtree(c, v);
    int last = dsm_fc_ahlt_color_leaf_last_subtree(c, v);
    if (cnt) *cnt = first >= 0 ? 1 : 0;
    if (total) *total = dsm_fc_ahlt_color_leaf_size(c);
    if (top) *top = dsm_fc_ahlt_topmarked(v, c);
    if (first_leaf) *first_leaf = first;
    if (last_leaf) *last_leaf = last;
    if (old_anchor) *old_anchor = dsm_fc_ahlt_nearest_change_ancestor(fc_parent[v], c);
    if (new_anchor) *new_anchor = dsm_fc_ahlt_nearest_change_ancestor(new_parent, c);
    return 0;
}

static int dsm_fc_ahlt_add_leaf(int parent, int leaf) {
    if (leaf < 0 || leaf >= fc_capacity) return -2;
    fc_active[leaf] = 1;
    fc_parent[leaf] = parent;
    return 0;
}

static int dsm_fc_ahlt_delete_leaf(int leaf) {
    if (leaf < 0 || leaf >= fc_capacity) return -2;
    fc_active[leaf] = 0;
    fc_parent[leaf] = -1;
    return 0;
}

static int dsm_fc_ahlt_link_subtree(int v, int new_parent) {
    if (v <= 0 || v >= fc_capacity || new_parent < 0 || new_parent >= fc_capacity) return -2;
    fc_parent[v] = new_parent;
    return 0;
}

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <limits.h>
#include <stddef.h>

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) { fprintf(stderr, "out of memory\n"); exit(1); }
    return p;
}

static void *xcalloc(size_t n, size_t size) {
    if (size && n > SIZE_MAX / size) {
        fprintf(stderr, "allocation size overflow\n"); exit(1);
    }
    void *p = calloc(n ? n : 1, size ? size : 1);
    if (!p) { fprintf(stderr, "out of memory\n"); exit(1); }
    return p;
}

static void *xrealloc(void *p, size_t n) {
    void *q = realloc(p, n ? n : 1);
    if (!q) { fprintf(stderr, "out of memory\n"); exit(1); }
    return q;
}

static void xfree(void *p) { free(p); }

#define MAXC 200010
#define MXL 20
#define MBS 14
#define MBT (1 << MBS)

static int N, Q, nC, capN;
static double alp;
static int *pa, *tin, *tout, tmr_;
static int *tinv;
static int *col;
static unsigned char *alive;
static int *free_nodes, free_top;
static int *chcnt;
static int *dlv, ndl;
static int *cL;
static int *cT;
static int *AP_;
static int *subsz0;
static int *bdep, *bes, *bed, *bef, beln;
static int brb, brn;
static int *brbm, *brbt, *brsp, *brlg;
static signed char brlu[MBT][MBS][MBS];
static char brlo[MBT];
static int build_static_topology;

enum {
    DSM_FC_OK = 0,
    DSM_FC_BAD_ARGUMENT = -1,
    DSM_FC_NEEDS_DYNAMIC_ORDER_BACKEND = -2
};

static int topo_depth(int v);
static int topo_subtree_size(int v);
static int topo_is_leaf(int v);
static int topo_contains_subtree(int root, int x);
static int color_order_backend_is_dynamic(void);
static int fc_nav_is_dynamic(void);
static void fc_nav_init(void);
static void fc_nav_clear(void);
static void fc_nav_mark(int v, int c, int pool_node);
static int fc_nav_topmarked(int v, int c);
static int fc_nav_add_leaf(int parent, int leaf);
static int fc_nav_delete_leaf(int leaf);
static int fc_nav_color_leaf_count_subtree(int c, int v);
static int fc_nav_prepare_subtree_move_color(int v, int new_parent, int c,
                                             int *cnt, int *total, int *top,
                                             int *first_leaf, int *last_leaf,
                                             int *old_anchor,
                                             int *new_anchor);
static void fc_nav_mark_color_leaf(int v, int c);
static void fc_nav_unmark_color_leaf(int v, int c);
static int sparse_count_color_in_subtree(int v, int c);
static void sparse_update_color(int v, int old_c, int new_c);
static int sparse_subtree_move(int v, int new_parent);
static int sparse_add_leaf_dynamic(int parent, int c);
static int sparse_remove_leaf_dynamic(int v);
static int dsm_fc_add_leaf(int parent, int c);
static int dsm_fc_remove_leaf(int v);

#define MC ((long long)MAXC)
static long long menc(int f, int c) { return (long long)f * MC + (MC - 1 - c); }
static int mf(long long e) { return (int)(e / MC); }
static int mc2(long long e) { return (int)(MC - 1 - e % MC); }

typedef struct TN {
    int k, h, sz;
    int l, r;
    long long mv;
} TN;

static TN *_tp;
static int _tp_cap;
static int _tp_cap_max;
static int _tn;
static int _fl;

static void tensure(int need) {
    int nc = _tp_cap;
    if (need < _tp_cap) return;
    while (nc <= need && nc < _tp_cap_max) {
        int nxt = nc << 1;
        if (nxt <= nc) {
            nc = _tp_cap_max;
            break;
        }
        if (nxt > _tp_cap_max) nxt = _tp_cap_max;
        nc = nxt;
    }
    if (need >= nc) {
        fprintf(stderr, "TPOOL\n");
        exit(1);
    }
    _tp = (TN *)xrealloc(_tp, (size_t)nc * sizeof(TN));
    _tp_cap = nc;
}

static int ta(int k, long long v) {
    int x;
    TN *t;
    if (_fl) {
        x = _fl;
        _fl = _tp[x].r;
    } else {
        tensure(_tn);
        x = _tn++;
    }
    t = &_tp[x];
    t->k = k;
    t->h = 1;
    t->sz = 1;
    t->mv = v;
    t->l = 0;
    t->r = 0;
    return x;
}

static void tf(int x) {
    if (x) {
        _tp[x].l = 0;
        _tp[x].r = _fl;
        _fl = x;
    }
}

static int tsz(int x) { return x ? _tp[x].sz : 0; }
static int tht(int x) { return x ? _tp[x].h : 0; }

static void tpu(int x) {
    TN *t;
    if (!x) return;
    t = &_tp[x];
    t->sz = 1 + tsz(t->l) + tsz(t->r);
    t->h = 1 + (tht(t->l) > tht(t->r) ? tht(t->l) : tht(t->r));
}

static int trrot(int y) {
    int x = _tp[y].l, z = _tp[x].r;
    _tp[x].r = y;
    _tp[y].l = z;
    tpu(y);
    tpu(x);
    return x;
}

static int tlrot(int x) {
    int y = _tp[x].r, z = _tp[y].l;
    _tp[y].l = x;
    _tp[x].r = z;
    tpu(x);
    tpu(y);
    return y;
}

static int tbal(int t) {
    int bf;
    if (!t) return 0;
    bf = tht(_tp[t].l) - tht(_tp[t].r);
    if (bf > 1) {
        if (tht(_tp[_tp[t].l].l) < tht(_tp[_tp[t].l].r)) _tp[t].l = tlrot(_tp[t].l);
        return trrot(t);
    }
    if (bf < -1) {
        if (tht(_tp[_tp[t].r].r) < tht(_tp[_tp[t].r].l)) _tp[t].r = trrot(_tp[t].r);
        return tlrot(t);
    }
    return t;
}

static int tins1(int r, int nd) {
    if (!r) return nd;
    if (_tp[nd].k < _tp[r].k) _tp[r].l = tins1(_tp[r].l, nd);
    else if (_tp[nd].k > _tp[r].k) _tp[r].r = tins1(_tp[r].r, nd);
    else {
        _tp[r].mv = _tp[nd].mv;
        tf(nd);
        tpu(r);
        return r;
    }
    tpu(r);
    return tbal(r);
}

static void tins(int *r, int k, long long v) { *r = tins1(*r, ta(k, v)); }

static int tdel1(int r, int k, int *did) {
    if (!r) return 0;
    if (k < _tp[r].k) _tp[r].l = tdel1(_tp[r].l, k, did);
    else if (k > _tp[r].k) _tp[r].r = tdel1(_tp[r].r, k, did);
    else {
        *did = 1;
        if (!_tp[r].l || !_tp[r].r) {
            int ch = _tp[r].l ? _tp[r].l : _tp[r].r;
            tf(r);
            return ch;
        }
        {
            int s = _tp[r].r;
            int dummy = 0;
            while (_tp[s].l) s = _tp[s].l;
            _tp[r].k = _tp[s].k;
            _tp[r].mv = _tp[s].mv;
            _tp[r].r = tdel1(_tp[r].r, _tp[s].k, &dummy);
        }
    }
    tpu(r);
    return tbal(r);
}

static void tdel(int *r, int k) {
    int did = 0;
    *r = tdel1(*r, k, &did);
}

static int tcle(int t, int k) {
    if (!t) return 0;
    if (_tp[t].k <= k) return 1 + tsz(_tp[t].l) + tcle(_tp[t].r, k);
    return tcle(_tp[t].l, k);
}

static int tcrng(int t, int lo, int hi) { return tcle(t, hi) - tcle(t, lo - 1); }

static int *_cb;
static int _cc;

static void tco(int t) {
    if (!t) return;
    tco(_tp[t].l);
    _cb[_cc++] = (int)_tp[t].mv;
    tco(_tp[t].r);
}

static void tco_pool(int t) {
    if (!t) return;
    tco_pool(_tp[t].l);
    _cb[_cc++] = (int)_tp[t].mv;
    tco_pool(_tp[t].r);
}

static int tbd_rec(int *ks, long long *vs, int l, int r) {
    int m, nd, left, right;
    if (l > r) return 0;
    m = (l + r) >> 1;
    nd = ta(ks[m], vs[m]);

    left = tbd_rec(ks, vs, l, m - 1);
    right = tbd_rec(ks, vs, m + 1, r);
    _tp[nd].l = left;
    _tp[nd].r = right;
    tpu(nd);
    return nd;
}

static int tbd(int *ks, long long *vs, int n) {
    if (!n) return 0;
    return tbd_rec(ks, vs, 0, n - 1);
}

static struct {
    int lc[2], lf;
    int lz;
    int lmx;
    int tc[2], th;
    long long tmx;
    int w, c, cnt, sd;
    int fch, nsb, prv, par;
} *P;
static int _p_cap;
static int _p_cap_max;
static int pn_, pfr_;

static void pensure(int need) {
    int nc = _p_cap;
    if (need < _p_cap) return;
    while (nc <= need && nc < _p_cap_max) {
        int nxt = nc << 1;
        if (nxt <= nc) {
            nc = _p_cap_max;
            break;
        }
        if (nxt > _p_cap_max) nxt = _p_cap_max;
        nc = nxt;
    }
    if (need >= nc) {
        fprintf(stderr, "NPOOL\n");
        exit(1);
    }
    P = xrealloc(P, (size_t)nc * sizeof(*P));
    _p_cap = nc;
}

static void pool_init(void) {
    pn_ = 1;
    pfr_ = 0;
}

static int pa2(int w, int c, int cnt) {
    int x;
    if (pfr_) {
        x = pfr_;
        pfr_ = P[x].tc[1];
    } else {
        pensure(pn_);
        x = pn_++;
    }
    memset(&P[x], 0, sizeof(P[0]));
    P[x].th = 1;
    P[x].tmx = menc(cnt, c);
    P[x].w = w;
    P[x].c = c;
    P[x].cnt = cnt;
    P[x].lmx = topo_depth(w);
    return x;
}

static void rt_link(int x, int y) {
    P[x].par = y;
    P[x].nsb = P[y].fch;
    P[x].prv = 0;
    if (P[y].fch) P[P[y].fch].prv = x;
    P[y].fch = x;
}

static int lr(int x) {
    int f = P[x].lf;
    return !f || (P[f].lc[0] != x && P[f].lc[1] != x);
}

static void lpull(int x) {
    int m;
    if (!x) return;

    m = topo_depth(P[x].w);
    if (P[x].lc[0] && P[P[x].lc[0]].lmx > m) m = P[P[x].lc[0]].lmx;
    if (P[x].lc[1] && P[P[x].lc[1]].lmx > m) m = P[P[x].lc[1]].lmx;
    P[x].lmx = m;
}

static void ladd_apply(int x, int delta) {
    if (!x) return;
    P[x].cnt += delta;
    P[x].tmx = menc(P[x].cnt, P[x].c);
    P[x].lz += delta;
}

static void lpush(int x) {
    int delta;
    if (!x || !P[x].lz) return;
    delta = P[x].lz;
    if (P[x].lc[0]) ladd_apply(P[x].lc[0], delta);
    if (P[x].lc[1]) ladd_apply(P[x].lc[1], delta);
    P[x].lz = 0;
}

static int *_lsp;
static void lpush_path(int x) {
    int sp = 0;
    int y = x;
    _lsp[sp++] = y;
    while (!lr(y)) {
        y = P[y].lf;
        if (sp >= _p_cap_max) break;
        _lsp[sp++] = y;
    }
    while (sp > 0) lpush(_lsp[--sp]);
}

static void lrot(int x) {
    int y = P[x].lf, z = P[y].lf, d = (P[y].lc[1] == x);
    if (!lr(y)) P[z].lc[P[z].lc[1] == y] = x;
    P[y].lc[d] = P[x].lc[d ^ 1];
    if (P[x].lc[d ^ 1]) P[P[x].lc[d ^ 1]].lf = y;
    P[x].lc[d ^ 1] = y;
    P[y].lf = x;
    P[x].lf = z;
    lpull(y);
    lpull(x);
}

static void lsplay(int x) {
    int guard = 0;
    lpush_path(x);
    while (!lr(x)) {
        if (++guard > _p_cap_max) {
            fprintf(stderr, "single-color LCT cycle in lsplay x=%d color=%d vertex=%d\n",
                    x, P[x].c, P[x].w);
            abort();
        }
        int y = P[x].lf;
        if (!lr(y)) {
            int z = P[y].lf;
            if ((P[z].lc[0] == y) == (P[y].lc[0] == x)) lrot(y);
            else lrot(x);
        }
        lrot(x);
    }
}

static void laccess(int x) {
    int la = 0, y, guard = 0;
    for (y = x; y; y = P[y].lf) {
        if (++guard > _p_cap_max) {
            fprintf(stderr, "single-color LCT cycle in laccess x=%d y=%d color=%d vertex=%d\n",
                    x, y, P[y].c, P[y].w);
            abort();
        }
        lsplay(y);
        lpush(y);
        P[y].lc[1] = la;
        lpull(y);
        la = y;
    }
    lsplay(x);
}

static void lct_init_singleton(int x) {
    P[x].lc[0] = 0;
    P[x].lc[1] = 0;
    P[x].lz = 0;
    P[x].lmx = topo_depth(P[x].w);
}

static void lct_init_attach(int child, int parent) {
    P[child].lf = parent;
    rt_link(child, parent);
}

static int lget_cnt(int x) {
    if (!x) return 0;
    laccess(x);
    return P[x].cnt;
}

static int *ot_lc0, *ot_lc1, *ot_lf, *ot_sz, *ot_val, *ot_lz, *ot_sp;

static int ot_left(int x) { return (x < 0) ? -1 : ot_lc0[x]; }
static int ot_right(int x) { return (x < 0) ? -1 : ot_lc1[x]; }
static void ot_set_left(int x, int y) { ot_lc0[x] = y; if (y >= 0) ot_lf[y] = x; }
static void ot_set_right(int x, int y) { ot_lc1[x] = y; if (y >= 0) ot_lf[y] = x; }

static int ot_size(int x) { return (x < 0) ? 0 : ot_sz[x]; }

static void ot_pull(int x) {
    if (x < 0) return;
    ot_sz[x] = 1 + ot_size(ot_lc0[x]) + ot_size(ot_lc1[x]);
}

static void ot_apply_add(int x, int delta) {
    if (x < 0) return;
    ot_val[x] += delta;
    ot_lz[x] += delta;
}

static void ot_push(int x) {
    int delta;
    if (x < 0 || !ot_lz[x]) return;
    delta = ot_lz[x];
    ot_apply_add(ot_lc0[x], delta);
    ot_apply_add(ot_lc1[x], delta);
    ot_lz[x] = 0;
}

static int ot_aux_root(int x) {
    int f = ot_lf[x];
    return f < 0 || (ot_lc0[f] != x && ot_lc1[f] != x);
}

static void ot_push_path(int x) {
    int sp = 0, y = x;
    ot_sp[sp++] = y;
    while (!ot_aux_root(y)) {
        y = ot_lf[y];
        ot_sp[sp++] = y;
    }
    while (sp > 0) ot_push(ot_sp[--sp]);
}

static void ot_rot(int x) {
    int y = ot_lf[x], z = ot_lf[y], d = (ot_lc1[y] == x);
    if (!ot_aux_root(y)) {
        if (ot_lc0[z] == y) ot_lc0[z] = x;
        else ot_lc1[z] = x;
    }
    if (d) {
        int b = ot_left(x);
        ot_set_right(y, b);
        ot_set_left(x, y);
    } else {
        int b = ot_right(x);
        ot_set_left(y, b);
        ot_set_right(x, y);
    }
    ot_lf[x] = z;
    ot_pull(y);
    ot_pull(x);
}

static void ot_splay(int x) {
    ot_push_path(x);
    while (!ot_aux_root(x)) {
        int y = ot_lf[x];
        if (!ot_aux_root(y)) {
            int z = ot_lf[y];
            if ((ot_lc0[z] == y) == (ot_lc0[y] == x)) ot_rot(y);
            else ot_rot(x);
        }
        ot_rot(x);
    }
}

static int ot_access(int x) {
    int la = -1, y, last = -1;
    for (y = x; y >= 0; y = ot_lf[y]) {
        ot_splay(y);
        ot_push(y);
        ot_lc1[y] = la;
        if (la >= 0) ot_lf[la] = y;
        ot_pull(y);
        last = y;
        la = y;
    }
    ot_splay(x);
    return last;
}

static void ot_init(void) {
    int i;
    for (i = 0; i < N; i++) {
        ot_lc0[i] = -1;
        ot_lc1[i] = -1;
        ot_lf[i] = pa[i];
        ot_sz[i] = 1;
        ot_val[i] = subsz0[i];
        ot_lz[i] = 0;
    }
}

static int ot_lca(int u, int v) {
    if (u == v) return u;
    ot_access(u);
    return ot_access(v);
}

static void ot_cut_from_parent(int child) {
    ot_access(child);
    if (ot_lc0[child] >= 0) {
        ot_lf[ot_lc0[child]] = -1;
        ot_lc0[child] = -1;
        ot_pull(child);
    }
}

static void ot_link_to_parent(int child, int parent) {
    ot_access(child);
    ot_access(parent);
    ot_lf[child] = parent;
}

static int ot_depth(int v) {
    ot_access(v);
    return ot_size(ot_lc0[v]);
}

static int ot_subtree_size(int v) {
    ot_access(v);
    return ot_val[v];
}

static void ot_path_add_root_to(int v, int delta) {
    if (v < 0 || !delta) return;
    ot_access(v);
    ot_apply_add(v, delta);
}

static int dsm_fc_subtree_move(int v, int new_parent) {
    if (v <= 0 || v >= N || new_parent < 0 || new_parent >= N) return DSM_FC_BAD_ARGUMENT;
    if ((!color_order_backend_is_dynamic()) &&
        topo_contains_subtree(v, new_parent)) {
        return DSM_FC_BAD_ARGUMENT;
    }
    return sparse_subtree_move(v, new_parent);
}

static int *hd, *nx, *to, ec;

static void ae(int u, int v) {
    to[ec] = v;
    nx[ec] = hd[u];
    hd[u] = ec++;
    to[ec] = u;
    nx[ec] = hd[v];
    hd[v] = ec++;
}

static int *_ds, *_di;
static void dfs(void) {
    int sp = 0;
    _ds[0] = 0;
    _di[0] = hd[0];
    pa[0] = -1;
    bdep[0] = 0;
    subsz0[0] = 1;
    tin[0] = tmr_++;
    tinv[tin[0]] = 0;
    bef[0] = beln;
    bes[beln] = 0;
    bed[beln] = 0;
    beln++;
    while (sp >= 0) {
        int u = _ds[sp];
        if (_di[sp] != -1) {
            int e = _di[sp];
            int v;
            _di[sp] = nx[e];
            v = to[e];
            if (v == pa[u]) continue;
            pa[v] = u;
            chcnt[u]++;
            bdep[v] = bdep[u] + 1;
            subsz0[v] = 1;
            sp++;
            _ds[sp] = v;
            _di[sp] = hd[v];
            tin[v] = tmr_++;
            tinv[tin[v]] = v;
            bef[v] = beln;
            bes[beln] = v;
            bed[beln] = bdep[v];
            beln++;
        } else {
            if (topo_is_leaf(u)) dlv[ndl++] = u;
            tout[u] = tmr_++;
            sp--;
            if (pa[u] >= 0) subsz0[pa[u]] += subsz0[u];
            if (sp >= 0) {
                int p2 = _ds[sp];
                bes[beln] = p2;
                bed[beln] = bdep[p2];
                beln++;
            }
        }
    }
}

#define BRSP(level, idx) brsp[(size_t)(level) * (size_t)brn + (size_t)(idx)]

static void build_lca_rmq(void) {
    int m = beln, b, j, i;
    if (m <= 1) {
        brb = 1;
        brn = m;
    } else {
        int lg = 1;
        while ((1 << lg) < m) lg++;
        brb = lg / 2;
        if (brb < 1) brb = 1;
        if (brb > MBS) brb = MBS;
        brn = (m + brb - 1) / brb;
    }
    brbm = (int *)xmalloc((size_t)(brn > 0 ? brn : 1) * sizeof(int));
    brbt = (int *)xmalloc((size_t)(brn > 0 ? brn : 1) * sizeof(int));
    brlg = (int *)xmalloc((size_t)(brn + 2) * sizeof(int));
    brsp = (int *)xmalloc((size_t)MXL * (size_t)(brn > 0 ? brn : 1) * sizeof(int));
    memset(brlo, 0, sizeof(brlo));
    for (b = 0; b < brn; b++) {
        int s = b * brb, e2 = s + brb, bl, tp = 0, mi;
        if (e2 > m) e2 = m;
        bl = e2 - s;
        for (i = 0; i < bl - 1; i++) if (bed[s + i + 1] > bed[s + i]) tp |= (1 << i);
        brbt[b] = tp;
        if (!brlo[tp]) {
            int v2[MBS];
            brlo[tp] = 1;
            v2[0] = 0;
            for (i = 0; i < brb - 1; i++) v2[i + 1] = v2[i] + ((tp & (1 << i)) ? 1 : -1);
            for (i = 0; i < brb; i++) {
                brlu[tp][i][i] = (signed char)i;
                for (j = i + 1; j < brb; j++) {
                    brlu[tp][i][j] =
                        (v2[j] < v2[(int)(unsigned char)brlu[tp][i][j - 1]]) ? (signed char)j : brlu[tp][i][j - 1];
                }
            }
        }
        mi = s;
        for (i = s + 1; i < e2; i++) if (bed[i] < bed[mi]) mi = i;
        brbm[b] = mi;
    }
    if (brn >= 1) brlg[1] = 0;
    for (i = 2; i <= brn; i++) brlg[i] = brlg[i / 2] + 1;
    for (b = 0; b < brn; b++) BRSP(0, b) = b;
    for (j = 1; (1 << j) <= brn; j++) {
        for (i = 0; i + (1 << j) <= brn; i++) {
            int a = BRSP(j - 1, i), b2 = BRSP(j - 1, i + (1 << (j - 1)));
            BRSP(j, i) = (bed[brbm[a]] <= bed[brbm[b2]]) ? a : b2;
        }
    }
}

static int build_rmq(int l, int r) {
    int bl = l / brb, br = r / brb;
    if (bl == br) return bl * brb + brlu[brbt[bl]][l - bl * brb][r - bl * brb];
    {
        int i1 = bl * brb + brlu[brbt[bl]][l - bl * brb][(bl + 1) * brb - 1 - bl * brb];
        int i2 = br * brb + brlu[brbt[br]][0][r - br * brb];
        int best = (bed[i1] <= bed[i2]) ? i1 : i2;
        if (bl + 1 < br) {
            int k = brlg[br - bl - 1];
            int a = BRSP(k, bl + 1), b2 = BRSP(k, br - (1 << k));
            int mb = (bed[brbm[a]] <= bed[brbm[b2]]) ? a : b2;
            if (bed[brbm[mb]] < bed[best]) best = brbm[mb];
        }
        return best;
    }
}

static int build_lca(int u, int v) {
    int l = bef[u], r = bef[v];
    if (l > r) {
        int t = l;
        l = r;
        r = t;
    }
    return bes[build_rmq(l, r)];
}

static void free_build_lca(void) {
    xfree(bdep);
    xfree(bes);
    xfree(bed);
    xfree(bef);
    xfree(brbm);
    xfree(brbt);
    xfree(brsp);
    xfree(brlg);
    bdep = bes = bed = bef = brbm = brbt = brsp = brlg = NULL;
}

static int topo_lca(int u, int v) {
    return build_static_topology ? build_lca(u, v) : ot_lca(u, v);
}

static int topo_depth(int v) { return build_static_topology ? bdep[v] : ot_depth(v); }

static int topo_subtree_size(int v) { return build_static_topology ? subsz0[v] : ot_subtree_size(v); }

static int topo_deeper_or_equal(int a, int b) { return topo_depth(a) >= topo_depth(b); }

static int topo_contains_subtree(int root, int x) {
    return topo_lca(root, x) == root;
}

static int topo_is_leaf(int v) { return chcnt[v] == 0; }

static int node_alive(int v) { return v >= 0 && v < N && (!alive || alive[v]); }

static int topo_order_key(int v) { return tin[v]; }

static int topo_subtree_last_key(int v) { return tout[v] - 1; }

static int topo_node_at_order_key(int k) { return tinv[k]; }

static void ot_init_single_node(int v, int parent) {
    ot_lc0[v] = -1;
    ot_lc1[v] = -1;
    ot_lf[v] = parent;
    ot_sz[v] = 1;
    ot_val[v] = 1;
    ot_lz[v] = 0;
}

static int dsm_fc_add_leaf(int parent, int c) {
    return sparse_add_leaf_dynamic(parent, c);
}

static int dsm_fc_remove_leaf(int v) {
    return sparse_remove_leaf_dynamic(v);
}

static int color_leaf_root(int c) { return cL[c]; }

static void color_leaf_set_root(int c, int root) { cL[c] = root; }

static void color_tree_set_root(int c, int root) { cT[c] = root; }

static int color_leaf_count_subtree(int c, int v) {
    if (color_order_backend_is_dynamic()) return fc_nav_color_leaf_count_subtree(c, v);
    return tcrng(color_leaf_root(c), topo_order_key(v), topo_subtree_last_key(v));
}

static void color_leaf_insert(int c, int v) {
    if (color_order_backend_is_dynamic()) {
        fc_nav_mark_color_leaf(v, c);
        return;
    }
    int root = color_leaf_root(c);
    tins(&root, topo_order_key(v), (long long)v);
    color_leaf_set_root(c, root);
}

static void color_leaf_delete(int c, int v) {
    if (color_order_backend_is_dynamic()) {
        fc_nav_unmark_color_leaf(v, c);
        return;
    }
    int root = color_leaf_root(c);
    tdel(&root, topo_order_key(v));
    color_leaf_set_root(c, root);
}

static void fc_nav_init(void) {
    dsm_fc_ahlt_init(capN, nC, N, pa, alive);
}

static int fc_nav_is_dynamic(void) {
    return dsm_fc_ahlt_is_dynamic();
}

static void fc_nav_clear(void) {
    dsm_fc_ahlt_clear_marks();
}

static void fc_nav_mark(int v, int c, int pool_node) {
    dsm_fc_ahlt_mark(v, c, pool_node);
}

static int fc_nav_topmarked(int v, int c) {
    return dsm_fc_ahlt_topmarked(v, c);
}

static int fc_nav_add_leaf(int parent, int leaf) {
    return dsm_fc_ahlt_add_leaf(parent, leaf);
}

static int fc_nav_delete_leaf(int leaf) {
    return dsm_fc_ahlt_delete_leaf(leaf);
}

static int fc_nav_color_leaf_count_subtree(int c, int v) {
    return dsm_fc_ahlt_color_leaf_count_subtree(c, v);
}

static int fc_nav_prepare_subtree_move_color(
    int v, int new_parent, int c,
    int *cnt, int *total, int *top,
    int *first_leaf, int *last_leaf,
    int *old_anchor,
    int *new_anchor) {
    return dsm_fc_ahlt_prepare_subtree_move_color(v, new_parent, c, cnt,
                                                  total, top, first_leaf,
                                                  last_leaf, old_anchor,
                                                  new_anchor);
}

static void fc_nav_mark_color_leaf(int v, int c) {
    dsm_fc_ahlt_mark_color_leaf(v, c);
}

static void fc_nav_unmark_color_leaf(int v, int c) {
    dsm_fc_ahlt_unmark_color_leaf(v, c);
}

static int color_order_backend_is_dynamic(void) { return fc_nav_is_dynamic(); }

static int *tcb, *tcf, *tcp, *tcd, tcn;
static int *_vs, *_vc;
static int *_vidx;

static void comp_tc(int root) {
    int nl, sp, i;
    tcn = 0;
    _cc = 0;
    tco(root);
    nl = _cc;
    if (!nl) return;
    sp = 0;
    for (i = 0; i < nl; i++) {
        int v = _cb[i];
        if (!sp) {
            _vs[sp] = v;
            _vc[sp] = 1;
            sp++;
            continue;
        }
        {
            int a = topo_lca(v, _vs[sp - 1]);
            while (sp >= 2 && topo_deeper_or_equal(_vs[sp - 2], a)) {
                _vc[sp - 2] += _vc[sp - 1];
                tcb[tcn] = _vs[sp - 1];
                tcf[tcn] = _vc[sp - 1];
                tcp[tcn] = _vs[sp - 2];
                tcn++;
                sp--;
            }
            if (_vs[sp - 1] != a) {
                int c = _vc[sp - 1];
                tcb[tcn] = _vs[sp - 1];
                tcf[tcn] = c;
                tcp[tcn] = a;
                tcn++;
                _vs[sp - 1] = a;
                _vc[sp - 1] = c;
            }
        }
        _vs[sp] = v;
        _vc[sp] = 1;
        sp++;
    }
    while (sp >= 2) {
        _vc[sp - 2] += _vc[sp - 1];
        tcb[tcn] = _vs[sp - 1];
        tcf[tcn] = _vc[sp - 1];
        tcp[tcn] = _vs[sp - 2];
        tcn++;
        sp--;
    }
    if (sp > 0) {
        tcb[tcn] = _vs[0];
        tcf[tcn] = _vc[0];
        tcp[tcn] = -1;
        tcn++;
    }
    for (i = 0; i < tcn; i++) {
        tcd[i] = 0;
        _vidx[tcb[i]] = i;
    }
    for (i = 0; i < tcn; i++) {
        int p2 = tcp[i];
        if (p2 < 0) continue;
        tcd[_vidx[p2]]++;
    }
}

static int sparse_count_color_in_subtree(int v, int c) {
    if (color_order_backend_is_dynamic()) {
        return color_leaf_count_subtree(c, v);
    }
    int x = fc_nav_topmarked(v, c);
    if (x <= 0) return 0;
    return lget_cnt(x);
}

static void sparse_update_color(int v, int old_c, int new_c) {
    color_leaf_delete(old_c, v);

    col[v] = new_c;
    color_leaf_insert(new_c, v);
}

static int sparse_add_leaf_dynamic(int parent, int c) {
    int v, parent_was_leaf, rc;
    if (!color_order_backend_is_dynamic()) return DSM_FC_NEEDS_DYNAMIC_ORDER_BACKEND;
    if (!node_alive(parent) || c < 0 || c >= nC) return DSM_FC_BAD_ARGUMENT;
    if (free_top > 0) v = free_nodes[free_top - 1];
    else {
        if (N >= capN) return DSM_FC_BAD_ARGUMENT;
        v = N;
    }

    parent_was_leaf = topo_is_leaf(parent);
    if (parent_was_leaf) {
        color_leaf_delete(col[parent], parent);
    }

    rc = fc_nav_add_leaf(parent, v);
    if (rc != DSM_FC_OK) return rc;

    if (free_top > 0) free_top--;
    else N++;

    alive[v] = 1;
    pa[v] = parent;
    chcnt[v] = 0;
    col[v] = c;
    tin[v] = -1;
    tout[v] = -1;
    subsz0[v] = 1;
    ot_init_single_node(v, -1);

    ot_path_add_root_to(parent, 1);
    ot_link_to_parent(v, parent);
    chcnt[parent]++;

    color_leaf_insert(c, v);
    return v;
}

static int sparse_remove_leaf_dynamic(int v) {
    int c, parent, parent_becomes_leaf, rc;
    if (!color_order_backend_is_dynamic()) return DSM_FC_NEEDS_DYNAMIC_ORDER_BACKEND;
    if (v <= 0 || !node_alive(v) || !topo_is_leaf(v)) return DSM_FC_BAD_ARGUMENT;
    parent = pa[v];
    if (parent < 0 || !node_alive(parent)) return DSM_FC_BAD_ARGUMENT;

    c = col[v];
    parent_becomes_leaf = (chcnt[parent] == 1);
    color_leaf_delete(c, v);

    rc = fc_nav_delete_leaf(v);
    if (rc != DSM_FC_OK) return rc;

    ot_path_add_root_to(parent, -1);
    ot_cut_from_parent(v);
    chcnt[parent]--;
    alive[v] = 0;
    pa[v] = -1;
    chcnt[v] = 0;
    free_nodes[free_top++] = v;

    if (parent_becomes_leaf) {
        color_leaf_insert(col[parent], parent);
    }

    return DSM_FC_OK;
}

static int sparse_subtree_move(int v, int new_parent) {
    int old_parent;
    if (v <= 0 || !node_alive(v) || !node_alive(new_parent)) return DSM_FC_BAD_ARGUMENT;
    if (!color_order_backend_is_dynamic() && topo_contains_subtree(v, new_parent)) return DSM_FC_BAD_ARGUMENT;
    old_parent = pa[v];
    if (old_parent < 0) return DSM_FC_BAD_ARGUMENT;
    if (old_parent == new_parent) return DSM_FC_OK;

    {
        int moved_size = topo_subtree_size(v);
        int new_parent_was_leaf = topo_is_leaf(new_parent);
        int *mv_cnt = (int *)xcalloc((size_t)nC, sizeof(int));
        int *mv_total = (int *)xcalloc((size_t)nC, sizeof(int));
        int *mv_top = (int *)xcalloc((size_t)nC, sizeof(int));
        int *mv_first = (int *)xmalloc((size_t)nC * sizeof(int));
        int *mv_last = (int *)xmalloc((size_t)nC * sizeof(int));
        int *mv_old_anchor = (int *)xmalloc((size_t)nC * sizeof(int));
        int *mv_new_anchor = (int *)xmalloc((size_t)nC * sizeof(int));
        int c, rc;

        if (new_parent_was_leaf) {
            color_leaf_delete(col[new_parent], new_parent);
        }

        for (c = 0; c < nC; c++) {
            mv_first[c] = -1;
            mv_last[c] = -1;
            mv_old_anchor[c] = -1;
            mv_new_anchor[c] = -1;
            rc = fc_nav_prepare_subtree_move_color(v, new_parent, c,
                                                   &mv_cnt[c], &mv_total[c],
                                                   &mv_top[c], &mv_first[c],
                                                   &mv_last[c],
                                                   &mv_old_anchor[c],
                                                   &mv_new_anchor[c]);
            if (rc != DSM_FC_OK) {
                xfree(mv_cnt);
                xfree(mv_total);
                xfree(mv_top);
                xfree(mv_first);
                xfree(mv_last);
                xfree(mv_old_anchor);
                xfree(mv_new_anchor);
                return rc;
            }
        }

        for (c = 0; c < nC; c++) {
            (void)c;
        }

        rc = dsm_fc_ahlt_link_subtree(v, new_parent);
        if (rc != DSM_FC_OK) {
            xfree(mv_cnt);
            xfree(mv_total);
            xfree(mv_top);
            xfree(mv_first);
            xfree(mv_last);
            xfree(mv_old_anchor);
            xfree(mv_new_anchor);
            return rc;
        }

        ot_path_add_root_to(old_parent, -moved_size);
        ot_path_add_root_to(new_parent, moved_size);
        ot_cut_from_parent(v);
        chcnt[old_parent]--;
        chcnt[new_parent]++;
        pa[v] = new_parent;
        ot_link_to_parent(v, new_parent);

        for (c = 0; c < nC; c++) {
            (void)c;
        }

        if (chcnt[old_parent] == 0) {
            color_leaf_insert(col[old_parent], old_parent);
        }
        xfree(mv_cnt);
        xfree(mv_total);
        xfree(mv_top);
        xfree(mv_first);
        xfree(mv_last);
        xfree(mv_old_anchor);
        xfree(mv_new_anchor);
        return DSM_FC_OK;
    }
}

static void dsm_build(void) {
    int c, w, i;
    int *bk, *bc, *bo, *bt, *ar_head, *ar_nxt, *ct_head, *ct_tail, *ct_nxt, *apb, *mp2;
    long long *bv;

    (void)alp;
    bk = (int *)xmalloc((size_t)N * 3 * sizeof(int));
    bv = (long long *)xmalloc((size_t)N * 3 * sizeof(long long));
    bc = (int *)xcalloc((size_t)nC, sizeof(int));
    bo = (int *)xmalloc((size_t)nC * sizeof(int));
    bt = (int *)xcalloc((size_t)nC, sizeof(int));
    ar_head = (int *)xcalloc((size_t)N, sizeof(int));
    ar_nxt = (int *)xmalloc((size_t)_p_cap_max * sizeof(int));
    ct_head = (int *)xcalloc((size_t)nC, sizeof(int));
    ct_tail = (int *)xcalloc((size_t)nC, sizeof(int));
    ct_nxt = (int *)xmalloc((size_t)_p_cap_max * sizeof(int));
    apb = (int *)xmalloc((size_t)N * sizeof(int));
    mp2 = (int *)xmalloc((size_t)N * sizeof(int));

    memset(cL, 0, (size_t)nC * sizeof(int));
    memset(cT, 0, (size_t)nC * sizeof(int));
    fc_nav_clear();
    for (i = 0; i < ndl; i++) {
        int c2 = col[dlv[i]];
        if (c2 >= 0 && c2 < nC) bc[c2]++;
    }
    bo[0] = 0;
    for (c = 1; c < nC; c++) bo[c] = bo[c - 1] + bc[c - 1];
    for (i = 0; i < ndl; i++) {
        int vv = dlv[i], c2 = col[vv];
        int idx;
        if (c2 < 0 || c2 >= nC) continue;
        idx = bo[c2] + bt[c2]++;
        bk[idx] = topo_order_key(vv);
        bv[idx] = (long long)vv;
    }
    for (c = 0; c < nC; c++) if (bc[c] > 0) {
        int root;
        root = tbd(bk + bo[c], bv + bo[c], bc[c]);
        color_leaf_set_root(c, root);
    }
    for (i = 0; i < ndl; i++) {
        int vv = dlv[i], c2 = col[vv];
        if (c2 >= 0 && c2 < nC) fc_nav_mark_color_leaf(vv, c2);
    }

    for (w = 0; w < N; w++) {
        AP_[w] = 0;
    }

    for (c = nC - 1; c >= 0; c--) {
        if (!color_leaf_root(c)) continue;
        comp_tc(color_leaf_root(c));
        for (i = 0; i < tcn; i++) {
            int x;
            w = tcb[i];
            x = pa2(w, c, tcf[i]);
            P[x].sd = tcd[i];
            lct_init_singleton(x);
            mp2[w] = x;
            ar_nxt[x] = ar_head[w];
            ar_head[w] = x;
        }
        for (i = 0; i < tcn; i++) {
            int pw = tcp[i];
            if (pw < 0) continue;
            lct_init_attach(mp2[tcb[i]], mp2[pw]);
        }
    }

    for (w = 0; w < N; w++) {
        int acnt = 0, x;
        for (x = ar_head[w]; x; x = ar_nxt[x]) apb[acnt++] = x;
        AP_[w] = 0;
        if (acnt > 0) {
            int j;
            for (j = 0; j < acnt; j++) {
                bk[j] = P[apb[j]].c;
                bv[j] = apb[j];
            }
            AP_[w] = tbd(bk, bv, acnt);
        }
    }

    for (i = 0; i < tmr_; i++) {
        int ww = topo_node_at_order_key(i);
        if (ww < 0) continue;
        _cc = 0;
        tco_pool(AP_[ww]);
        for (w = 0; w < _cc; w++) {
            int px = _cb[w];
            int cc = P[px].c;
            ct_nxt[px] = 0;
            if (!ct_head[cc]) ct_head[cc] = px;
            else ct_nxt[ct_tail[cc]] = px;
            ct_tail[cc] = px;
        }
    }

    for (c = 0; c < nC; c++) {
        int cnt = 0, x;
        for (x = ct_head[c]; x; x = ct_nxt[x]) apb[cnt++] = x;
        if (cnt > 0) {
            int j;
            for (j = 0; j < cnt; j++) {
                bk[j] = topo_order_key(P[apb[j]].w);
                bv[j] = apb[j];
            }
            color_tree_set_root(c, tbd(bk, bv, cnt));
            for (j = 0; j < cnt; j++) {
                fc_nav_mark(P[apb[j]].w, c, apb[j]);
            }
        }
    }

    xfree(bk);
    xfree(bv);
    xfree(bc);
    xfree(bo);
    xfree(bt);
    xfree(ar_head);
    xfree(ar_nxt);
    xfree(ct_head);
    xfree(ct_tail);
    xfree(ct_nxt);
    xfree(apb);
    xfree(mp2);
}

static void query_impl(int v, int *rf, int *rc) {
    int c;
    long long b = -1;
    for (c = 0; c < nC; c++) {
        int fc = sparse_count_color_in_subtree(v, c);
        if (fc > 0) {
            long long e2 = menc(fc, c);
            if (e2 > b) b = e2;
        }
    }
    if (b < 0) {
        *rf = 0;
        *rc = -1;
    } else {
        *rf = mf(b);
        *rc = mc2(b);
    }
}

static void update_impl(int v, int co, int cn) {
    if (!node_alive(v) || !topo_is_leaf(v) || co == cn) return;

    sparse_update_color(v, co, cn);
}

static int valid_tree(int n, int C, const int *parents, const int *colors) {
    if (n < 1 || C < 1 || !parents || !colors) return 0;
    for (int v = 0; v < n; v++) {
        if (colors[v] < 0 || colors[v] >= C) return 0;
        if (v && (parents[v] < 0 || parents[v] >= n || parents[v] == v)) return 0;
    }
    unsigned char *state = xcalloc((size_t)n, 1);
    state[0] = 2;
    for (int v = 1; v < n; v++) {
        int u = v;
        while (state[u] == 0) {
            state[u] = 1;
            u = parents[u];
        }
        if (state[u] == 1) { xfree(state); return 0; }
        u = v;
        while (state[u] == 1) {
            state[u] = 2;
            u = parents[u];
        }
    }
    xfree(state);
    return 1;
}

void fdsm_destroy(void) {
    free(mark_pool.node);
    free(leaf_pool.node);
    free(fc_parent);
    free(fc_active);
    free(fc_leaf_color);
    free(fc_leaf_count);
    free(pa);
    free(tin);
    free(tout);
    free(tinv);
    free(col);
    free(alive);
    free(free_nodes);
    free(chcnt);
    free(dlv);
    free(cL);
    free(cT);
    free(AP_);
    free(subsz0);
    free(bdep);
    free(bes);
    free(bed);
    free(bef);
    free(brbm);
    free(brbt);
    free(brsp);
    free(brlg);
    free(_tp);
    free(_cb);
    free(P);
    free(_lsp);
    free(ot_lc0);
    free(ot_lc1);
    free(ot_lf);
    free(ot_sz);
    free(ot_val);
    free(ot_lz);
    free(ot_sp);
    free(hd);
    free(nx);
    free(to);
    free(_ds);
    free(_di);
    free(tcb);
    free(tcf);
    free(tcp);
    free(tcd);
    free(_vs);
    free(_vc);
    free(_vidx);
    api_ready = 0;
    memset(&mark_pool, 0, sizeof(mark_pool));
    memset(&leaf_pool, 0, sizeof(leaf_pool));
    fc_capacity = 0;
    fc_ncolors = 0;
    fc_parent = NULL;
    fc_active = NULL;
    fc_leaf_color = NULL;
    fc_leaf_count = NULL;
    N = 0;
    Q = 0;
    nC = 0;
    capN = 0;
    alp = 0;
    pa = NULL;
    tin = NULL;
    tout = NULL;
    tmr_ = 0;
    tinv = NULL;
    col = NULL;
    alive = NULL;
    free_nodes = NULL;
    free_top = 0;
    chcnt = NULL;
    dlv = NULL;
    ndl = 0;
    cL = NULL;
    cT = NULL;
    AP_ = NULL;
    subsz0 = NULL;
    bdep = NULL;
    bes = NULL;
    bed = NULL;
    bef = NULL;
    beln = 0;
    brb = 0;
    brn = 0;
    brbm = NULL;
    brbt = NULL;
    brsp = NULL;
    brlg = NULL;
    memset(brlu, 0, sizeof(brlu));
    memset(brlo, 0, sizeof(brlo));
    build_static_topology = 0;
    _tp = NULL;
    _tp_cap = 0;
    _tp_cap_max = 0;
    _tn = 0;
    _fl = 0;
    _cb = NULL;
    _cc = 0;
    P = NULL;
    _p_cap = 0;
    _p_cap_max = 0;
    pn_ = 0;
    pfr_ = 0;
    _lsp = NULL;
    ot_lc0 = NULL;
    ot_lc1 = NULL;
    ot_lf = NULL;
    ot_sz = NULL;
    ot_val = NULL;
    ot_lz = NULL;
    ot_sp = NULL;
    hd = NULL;
    nx = NULL;
    to = NULL;
    ec = 0;
    _ds = NULL;
    _di = NULL;
    tcb = NULL;
    tcf = NULL;
    tcp = NULL;
    tcd = NULL;
    tcn = 0;
    _vs = NULL;
    _vc = NULL;
    _vidx = NULL;
}

int fdsm_init(int n, int C, double alpha, int max_operations, const int *parents, const int *colors) {
    int i;
    if (n < 1 || C < 1 || !isfinite(alpha) || alpha < 0.0 || alpha > 1.0) return -1;
    if (C >= MAXC || max_operations < 0 || n > (INT_MAX - 16) / 8 - 5 || max_operations > (INT_MAX - 16) / 8 - n - 5) return -1;
    if (!valid_tree(n, C, parents, colors)) return -1;
    fdsm_destroy();
    N = n;
    nC = C;
    alp = alpha;
    Q = max_operations;
    capN = N + Q + 5;

    _tp_cap_max = N * 6 + 8;
    _tp_cap = (_tp_cap_max < 16) ? _tp_cap_max : 16;
    _tp = (TN *)xmalloc((size_t)_tp_cap * sizeof(TN));
    _p_cap_max = N * 5 + 8;
    _p_cap = (_p_cap_max < 16) ? _p_cap_max : 16;
    P = xcalloc((size_t)_p_cap, sizeof(*P));
    _cb = (int *)xmalloc((size_t)N * sizeof(int));
    _lsp = (int *)xmalloc((size_t)_p_cap_max * sizeof(int));
    ot_lc0 = (int *)xmalloc((size_t)capN * sizeof(int));
    ot_lc1 = (int *)xmalloc((size_t)capN * sizeof(int));
    ot_lf = (int *)xmalloc((size_t)capN * sizeof(int));
    ot_sz = (int *)xmalloc((size_t)capN * sizeof(int));
    ot_val = (int *)xmalloc((size_t)capN * sizeof(int));
    ot_lz = (int *)xcalloc((size_t)capN, sizeof(int));
    ot_sp = (int *)xmalloc((size_t)capN * sizeof(int));
    hd = (int *)xmalloc((size_t)capN * sizeof(int));
    nx = (int *)xmalloc((size_t)(2 * capN) * sizeof(int));
    to = (int *)xmalloc((size_t)(2 * capN) * sizeof(int));
    pa = (int *)xmalloc((size_t)capN * sizeof(int));
    tin = (int *)xmalloc((size_t)capN * sizeof(int));
    tout = (int *)xmalloc((size_t)capN * sizeof(int));
    tinv = (int *)xmalloc((size_t)(2 * capN) * sizeof(int));
    chcnt = (int *)xcalloc((size_t)capN, sizeof(int));
    col = (int *)xmalloc((size_t)capN * sizeof(int));
    alive = (unsigned char *)xcalloc((size_t)capN, sizeof(unsigned char));
    free_nodes = (int *)xmalloc((size_t)capN * sizeof(int));
    dlv = (int *)xmalloc((size_t)capN * sizeof(int));
    bdep = (int *)xmalloc((size_t)capN * sizeof(int));
    bes = (int *)xmalloc((size_t)(2 * capN) * sizeof(int));
    bed = (int *)xmalloc((size_t)(2 * capN) * sizeof(int));
    bef = (int *)xmalloc((size_t)capN * sizeof(int));
    _ds = (int *)xmalloc((size_t)capN * sizeof(int));
    _di = (int *)xmalloc((size_t)capN * sizeof(int));
    tcb = (int *)xmalloc((size_t)(2 * capN) * sizeof(int));
    tcf = (int *)xmalloc((size_t)(2 * capN) * sizeof(int));
    tcp = (int *)xmalloc((size_t)(2 * capN) * sizeof(int));
    tcd = (int *)xmalloc((size_t)(2 * capN) * sizeof(int));
    _vs = (int *)xmalloc((size_t)capN * sizeof(int));
    _vc = (int *)xmalloc((size_t)capN * sizeof(int));
    _vidx = (int *)xmalloc((size_t)capN * sizeof(int));
    cL = (int *)xcalloc((size_t)nC, sizeof(int));
    cT = (int *)xcalloc((size_t)nC, sizeof(int));
    AP_ = (int *)xcalloc((size_t)capN, sizeof(int));
    subsz0 = (int *)xcalloc((size_t)capN, sizeof(int));

    memset(hd, -1, (size_t)capN * sizeof(int));
    memset(tinv, -1, (size_t)(2 * capN) * sizeof(int));
    memset(tin, -1, (size_t)capN * sizeof(int));
    memset(tout, -1, (size_t)capN * sizeof(int));
    ec = 0;
    tmr_ = 0;
    beln = 0;
    ndl = 0;
    pool_init();
    _tn = 1;
    pn_ = 1;
    _fl = 0;
    free_top = 0;
    for (i = 0; i < N; i++) alive[i] = 1;

    for (i = 1; i < N; i++) ae(parents[i], i);
    for (i = 0; i < N; i++) col[i] = colors[i];
    dfs();
    build_lca_rmq();
    ot_init();
    fc_nav_init();
    build_static_topology = 1;
    dsm_build();
    build_static_topology = 0;
    free_build_lca();
    api_ready = 1;
    return 0;
}

int fdsm_update(int v, int color) {
    if (!api_ready || !node_alive(v) || color < 0 || color >= nC) return -1;
    if (!topo_is_leaf(v)) return -1;
    update_impl(v, col[v], color);
    return 0;
}

int fdsm_query(int v, int *color, int *frequency) {
    if (!api_ready || !node_alive(v) || !color || !frequency) return -1;
    query_impl(v, frequency, color);
    return 0;
}

int fdsm_move(int v, int parent) {
    if (!api_ready || v <= 0 || !node_alive(v) || !node_alive(parent)) return -1;
    if (topo_contains_subtree(v, parent)) return -1;
    return dsm_fc_subtree_move(v, parent);
}

int fdsm_add_leaf(int parent, int color) {
    if (!api_ready || !node_alive(parent) || color < 0 || color >= nC) return -1;
    return dsm_fc_add_leaf(parent, color);
}

int fdsm_remove_leaf(int v) {
    if (!api_ready || v <= 0 || !node_alive(v) || !topo_is_leaf(v)) return -1;
    return dsm_fc_remove_leaf(v);
}
