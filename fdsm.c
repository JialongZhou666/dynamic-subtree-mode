/*
 * fdsm.c -- Fully Dynamic Subtree Mode, few-colors structure.
 *
 * Drop-in public API (identical semantics to fdsm_corrected.c):
 *   fdsm_init, fdsm_update, fdsm_query, fdsm_move,
 *   fdsm_add_leaf, fdsm_remove_leaf, fdsm_destroy.
 *
 * Implements the construction of Theorem 5: the Euler sequence of the tree
 * is kept in a balanced search tree, and for every color the entry tokens
 * of its leaves are kept in a balanced search tree ordered by Euler rank.
 * Both are randomized treaps, so all bounds hold in expectation:
 *   query, subtree move            O(C log^2 n)
 *   recolor, add leaf, remove leaf O(log^2 n)
 *   space                          O(n + max_operations)
 *   construction                   O(n + C)
 *
 * Engineering optimizations; none changes the bounds above:
 *  1. Euler positions are memoized: for every color key, the position of
 *     its entry token; for every Euler-tree node, the position where its
 *     subtree starts.  Each memo carries a version.  A structural change
 *     (leaf insertion/deletion, subtree move) maps old positions to new ones
 *     by a piecewise shift; the last FDSM_LOG such maps are logged, so a
 *     memo from a recent version is brought up to date by a few additions
 *     instead of a walk.  Euler-tree nodes whose subtree is changed by a
 *     split, merge or deletion (O(log n) per operation) are invalidated.
 *  2. Every per-color split of an update is performed in the Euler order
 *     *before* the sequence changes, so it reuses the memoized positions.
 *  3. Deletions (color keys, Euler tokens) are by handle, without searches.
 *  4. Rank walks read one tree node per level and stop at the first
 *     ancestor with a usable memo, memoizing the nodes they pass.
 *  5. Small subtrees are answered by scanning their Euler interval; for a
 *     move, the same scan finds the colors that occur in the moved subtree.
 *  6. A query counts a color with one shared descent, visits colors in
 *     decreasing global frequency, and stops as soon as no remaining color
 *     can beat the current answer (using the subtree's leaf count, which the
 *     Euler tree maintains).
 *  7. A move touches only colors occurring in the moved subtree.
 *  8. All treaps are built in linear time (Cartesian-tree construction).
 *
 * Semantics: ties go to the smallest color index; a node that becomes a
 * leaf (after Delete Leaf or a move) keeps its stored color; Add Leaf makes
 * the new leaf the last child of its parent; freed vertex ids are reused.
 *
 * Tuning: a subtree whose Euler interval has at most
 * FDSM_SCAN_BASE + FDSM_SCAN_PER_COLOR * C tokens is scanned.
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <math.h>

int fdsm_init(int n, int C, double alpha, int max_operations,
              const int *parents, const int *colors);
int fdsm_update(int v, int color);
int fdsm_query(int v, int *color, int *frequency);
int fdsm_move(int v, int parent);
int fdsm_add_leaf(int parent, int color);
int fdsm_remove_leaf(int v);
void fdsm_destroy(void);

#ifndef FDSM_SCAN_BASE
#define FDSM_SCAN_BASE 64
#endif
#ifndef FDSM_SCAN_PER_COLOR
#define FDSM_SCAN_PER_COLOR 32
#endif
#ifndef FDSM_LOG
#define FDSM_LOG 128           /* number of logged position maps; power of 2 */
#endif

/* Euler-sequence treap node: token 2v = entry of v, 2v+1 = exit of v.
   st/ep memoize the Euler position of the first token of its subtree
   (ep = version of the memo, 0 = none). */
typedef struct { int l, r, p, sz, lv, st; uint32_t ep; } ENode;
/* Color treap node, indexed by vertex; rk/ep memoize the Euler position
   of the entry token 2v (ep = version of the memo, 0 = none). */
typedef struct { int l, r, p, sz, rk; uint32_t ep; } TNode;

static ENode *E;           /* 2*cap tokens */
static uint32_t *Epri;
static unsigned char *Eleaf; /* 1 iff token is the entry token of a leaf */
static TNode *T;           /* cap vertices */
static uint32_t *Tpri;
static int *croot;         /* per color: root of its treap, -1 if empty */
static int *vcol, *vpar, *vch, *fstack;
static unsigned char *alive;
static int *order, *cntc, *touched, *stk, *pre;
static int eroot = -1, nv, nC, cap, ftop, ready, order_changes;
static uint32_t ver, rng;   /* ver: current version, never 0 */

/* Position maps of the last FDSM_LOG structural changes.
   kind 0: k tokens inserted at position q;  kind 1: tokens [q, q+k) deleted;
   kind 2: block [a, b] moved to just before old position q (q outside it). */
typedef struct { int kind, a, b, q, k; } PosMap;
static PosMap maplog[FDSM_LOG];

/* ------------------------------------------------------------------ */
static uint32_t rnd(void) {
    uint32_t x = rng;
    x ^= x << 13; x ^= x >> 17; x ^= x << 5;
    return rng = x;
}

static void *zalloc(size_t count, size_t item) {
    if (!count) count = 1;
    if (count > SIZE_MAX / item) return NULL;
    return calloc(count, item);
}

static inline int map_pos(const PosMap *m, int p) {
    switch (m->kind) {
    case 0:
        return p >= m->q ? p + m->k : p;
    case 1:
        return p >= m->q + m->k ? p - m->k : p;
    default: {
        int s = m->b - m->a + 1;
        if (m->q < m->a) {
            if (p < m->q || p > m->b) return p;
            return p >= m->a ? p - (m->a - m->q) : p + s;
        }
        if (p < m->a || p >= m->q) return p;
        return p <= m->b ? p + (m->q - 1 - m->b) : p - s;
    }
    }
}

/* Is a memo of version e usable (current, or translatable via the log)? */
static inline int memo_ok(uint32_t e) {
    return e != 0 && ver - e < (uint32_t)FDSM_LOG;
}

/* Bring a position memoized at version e to the current version. */
static inline int translate(int p, uint32_t e) {
    while (e != ver) { e++; p = map_pos(&maplog[e & (FDSM_LOG - 1)], p); }
    return p;
}

static void log_change(int kind, int a, int b, int q, int k) {
    if (++ver == 0) {                /* wrap-around: drop all memos */
        int v;
        for (v = 0; v < cap; v++) T[v].ep = 0;
        for (v = 0; v < 2 * cap; v++) E[v].ep = 0;
        ver = 1;
    }
    maplog[ver & (FDSM_LOG - 1)].kind = kind;
    maplog[ver & (FDSM_LOG - 1)].a = a;
    maplog[ver & (FDSM_LOG - 1)].b = b;
    maplog[ver & (FDSM_LOG - 1)].q = q;
    maplog[ver & (FDSM_LOG - 1)].k = k;
}

/* ------------------------- Euler treap ----------------------------- */
static inline int esz(int x) { return x < 0 ? 0 : E[x].sz; }
static inline int elv(int x) { return x < 0 ? 0 : E[x].lv; }
static inline void epull(int x) {
    E[x].sz = 1 + esz(E[x].l) + esz(E[x].r);
    E[x].lv = Eleaf[x] + elv(E[x].l) + elv(E[x].r);
    E[x].ep = 0;                       /* subtree changed: memo invalid */
}
static void enew(int x, int leaf) {
    E[x].l = E[x].r = E[x].p = -1;
    E[x].sz = 1;
    E[x].lv = leaf;
    E[x].ep = 0;
    Eleaf[x] = (unsigned char)leaf;
    Epri[x] = rnd();
}

static int emerge(int a, int b) {
    if (a < 0) { if (b >= 0) E[b].p = -1; return b; }
    if (b < 0) { E[a].p = -1; return a; }
    if (Epri[a] < Epri[b]) {
        int r = emerge(E[a].r, b);
        E[a].r = r; E[r].p = a; epull(a); E[a].p = -1;
        return a;
    } else {
        int l = emerge(a, E[b].l);
        E[b].l = l; E[l].p = b; epull(b); E[b].p = -1;
        return b;
    }
}

/* L receives the first k tokens. */
static void esplit(int x, int k, int *L, int *R) {
    int a, b;
    if (x < 0) { *L = *R = -1; return; }
    if (k <= esz(E[x].l)) {
        esplit(E[x].l, k, &a, &b);
        E[x].l = b; if (b >= 0) E[b].p = x;
        epull(x); E[x].p = -1;
        *L = a; *R = x;
    } else {
        esplit(E[x].r, k - esz(E[x].l) - 1, &a, &b);
        E[x].r = a; if (a >= 0) E[a].p = x;
        epull(x); E[x].p = -1;
        *L = x; *R = b;
    }
}

/* Rank of token e (number of tokens before it).  The walk reads one node
   per level and stops at the first ancestor with a usable memo of its
   subtree start; it then memoizes the starts of all nodes it passed. */
static int erank(int e) {
    int x = e, r = esz(E[x].l), k = 0, p, rank, i;
    for (;;) {
        uint32_t m = E[x].ep;
        if (m == ver) { rank = E[x].st + r; break; }
        if (memo_ok(m)) {
            E[x].st = translate(E[x].st, m);
            E[x].ep = ver;
            rank = E[x].st + r;
            break;
        }
        stk[k] = x; pre[k] = r; k++;
        if ((p = E[x].p) < 0) { rank = r; break; }
        if (E[p].r == x) r += E[p].sz - E[x].sz;
        x = p;
    }
    for (i = 0; i < k; i++) { E[stk[i]].st = rank - pre[i]; E[stk[i]].ep = ver; }
    return rank;
}

/* Rank of e and number of leaf-entry tokens before e. */
static int erank_lp(int e, int *lp) {
    int x = e, r = esz(E[x].l), l = elv(E[x].l), p;
    while ((p = E[x].p) >= 0) {
        if (E[p].r == x) { r += E[p].sz - E[x].sz; l += E[p].lv - E[x].lv; }
        x = p;
    }
    *lp = l;
    return r;
}

/* Delete token x by handle. */
static void edelete(int x) {
    int m = emerge(E[x].l, E[x].r), p = E[x].p, f = Eleaf[x], y;
    if (p < 0) {
        eroot = m;
        if (m >= 0) E[m].p = -1;
    } else {
        if (E[p].l == x) E[p].l = m; else E[p].r = m;
        if (m >= 0) E[m].p = p;
        for (y = p; y >= 0; y = E[y].p) { E[y].sz--; E[y].lv -= f; E[y].ep = 0; }
    }
}

static void eset_leaf(int e, int f) {
    int d = f - Eleaf[e], x;
    if (!d) return;
    Eleaf[e] = (unsigned char)f;
    for (x = e; x >= 0; x = E[x].p) E[x].lv += d;
}

/* In-order successor. */
static int enext(int x) {
    if (E[x].r >= 0) {
        x = E[x].r;
        while (E[x].l >= 0) x = E[x].l;
        return x;
    }
    while (E[x].p >= 0 && E[E[x].p].r == x) x = E[x].p;
    return E[x].p;
}

/* -------------------------- Color treaps --------------------------- */
static inline int tsz(int x) { return x < 0 ? 0 : T[x].sz; }
static inline void tpull(int x) { T[x].sz = 1 + tsz(T[x].l) + tsz(T[x].r); }
static void tnew(int v) {
    T[v].l = T[v].r = T[v].p = -1;
    T[v].sz = 1;
    T[v].ep = 0;
    Tpri[v] = rnd();
}

/* Memoized Euler rank of the entry token of key vertex x. */
static inline int key_rank(int x) {
    uint32_t m = T[x].ep;
    if (m != ver) {
        T[x].rk = memo_ok(m) ? translate(T[x].rk, m) : erank(2 * x);
        T[x].ep = ver;
    }
    return T[x].rk;
}

static int tmerge(int a, int b) {
    if (a < 0) { if (b >= 0) T[b].p = -1; return b; }
    if (b < 0) { T[a].p = -1; return a; }
    if (Tpri[a] < Tpri[b]) {
        int r = tmerge(T[a].r, b);
        T[a].r = r; T[r].p = a; tpull(a); T[a].p = -1;
        return a;
    } else {
        int l = tmerge(a, T[b].l);
        T[b].l = l; T[l].p = b; tpull(b); T[b].p = -1;
        return b;
    }
}

/* L receives the keys whose entry token precedes Euler position pos. */
static void tsplit(int x, int pos, int *L, int *R) {
    int a, b;
    if (x < 0) { *L = *R = -1; return; }
    if (key_rank(x) < pos) {
        tsplit(T[x].r, pos, &a, &b);
        T[x].r = a; if (a >= 0) T[a].p = x;
        tpull(x); T[x].p = -1;
        *L = x; *R = b;
    } else {
        tsplit(T[x].l, pos, &a, &b);
        T[x].l = b; if (b >= 0) T[b].p = x;
        tpull(x); T[x].p = -1;
        *L = a; *R = x;
    }
}

/* Insert vertex v into color c; pos = Euler position of v's entry token
   in the order in which the existing keys are compared. */
static void tinsert(int c, int v, int pos) {
    int a, b;
    tnew(v);
    tsplit(croot[c], pos, &a, &b);
    croot[c] = tmerge(tmerge(a, v), b);
    order_changes++;
}

/* Delete vertex v from color c by handle. */
static void tdelete(int v, int c) {
    int m = tmerge(T[v].l, T[v].r), p = T[v].p, y;
    if (p < 0) {
        croot[c] = m;
        if (m >= 0) T[m].p = -1;
    } else {
        if (T[p].l == v) T[p].l = m; else T[p].r = m;
        if (m >= 0) T[m].p = p;
        for (y = p; y >= 0; y = T[y].p) T[y].sz--;
    }
    T[v].l = T[v].r = T[v].p = -1;
    T[v].sz = 1;
    order_changes++;
}

/* Number of keys with Euler position in [lo, hi), one shared descent. */
static int tcount(int x, int lo, int hi) {
    int k, y, cnt;
    while (x >= 0) {
        k = key_rank(x);
        if (k < lo) x = T[x].r;
        else if (k >= hi) x = T[x].l;
        else break;
    }
    if (x < 0) return 0;
    cnt = 1;
    for (y = T[x].l; y >= 0; ) {
        if (key_rank(y) >= lo) { cnt += 1 + tsz(T[y].r); y = T[y].l; }
        else y = T[y].r;
    }
    for (y = T[x].r; y >= 0; ) {
        if (key_rank(y) < hi) { cnt += 1 + tsz(T[y].l); y = T[y].r; }
        else y = T[y].l;
    }
    return cnt;
}

static int tpresent(int x, int lo, int hi) {
    while (x >= 0) {
        int k = key_rank(x);
        if (k < lo) x = T[x].r;
        else if (k >= hi) x = T[x].l;
        else return 1;
    }
    return 0;
}

/* ---------------------- Color visiting order ----------------------- */
static inline int total(int c) { return croot[c] < 0 ? 0 : T[croot[c]].sz; }

static int order_cmp(const void *a, const void *b) {
    int x = *(const int *)a, y = *(const int *)b;
    int tx = total(x), ty = total(y);
    if (tx != ty) return tx > ty ? -1 : 1;
    return x < y ? -1 : (x > y);
}

static void sort_order(void) {
    int i, j;
    if (!order_changes) return;
    if (order_changes <= 8) {               /* nearly sorted */
        for (i = 1; i < nC; i++) {
            int c = order[i];
            for (j = i; j > 0 && order_cmp(&order[j - 1], &c) > 0; j--)
                order[j] = order[j - 1];
            order[j] = c;
        }
    } else {
        qsort(order, (size_t)nC, sizeof(int), order_cmp);
    }
    order_changes = 0;
}

/* --------------------------- Building ------------------------------ */
/* Cartesian-tree construction of an Euler treap from seq[0..m-1]. */
static int ebuild(const int *seq, int m) {
    int top = 0, i, np = 0, root;
    if (!m) return -1;
    for (i = 0; i < m; i++) {
        int x = seq[i], last = -1;
        while (top && Epri[stk[top - 1]] > Epri[x]) last = stk[--top];
        E[x].l = last;
        if (last >= 0) E[last].p = x;
        if (top) { E[stk[top - 1]].r = x; E[x].p = stk[top - 1]; }
        else E[x].p = -1;
        stk[top++] = x;
    }
    root = stk[0];
    top = 0;
    stk[top++] = root;
    while (top) {
        int x = stk[--top];
        pre[np++] = x;
        if (E[x].r >= 0) stk[top++] = E[x].r;
        if (E[x].l >= 0) stk[top++] = E[x].l;
    }
    for (i = np - 1; i >= 0; i--) epull(pre[i]);
    return root;
}

static int tbuild(const int *seq, int m) {
    int top = 0, i, np = 0, root;
    if (!m) return -1;
    for (i = 0; i < m; i++) {
        int x = seq[i], last = -1;
        while (top && Tpri[stk[top - 1]] > Tpri[x]) last = stk[--top];
        T[x].l = last;
        if (last >= 0) T[last].p = x;
        if (top) { T[stk[top - 1]].r = x; T[x].p = stk[top - 1]; }
        else T[x].p = -1;
        stk[top++] = x;
    }
    root = stk[0];
    top = 0;
    stk[top++] = root;
    while (top) {
        int x = stk[--top];
        pre[np++] = x;
        if (T[x].r >= 0) stk[top++] = T[x].r;
        if (T[x].l >= 0) stk[top++] = T[x].l;
    }
    for (i = np - 1; i >= 0; i--) tpull(pre[i]);
    return root;
}

/* ---------------------------- API ---------------------------------- */
static int valid_input(int n, int C, double alpha, int max_ops,
                       const int *parents, const int *colors) {
    int v;
    unsigned char *state;
    if (n <= 0 || C <= 0 || max_ops < 0 || !parents || !colors ||
        !isfinite(alpha) || alpha < 0.0 || alpha > 1.0 ||
        n > (INT_MAX - 16) / 2 - max_ops) return 0;
    for (v = 0; v < n; v++) {
        if (colors[v] < 0 || colors[v] >= C) return 0;
        if (v && (parents[v] < 0 || parents[v] >= n || parents[v] == v))
            return 0;
    }
    state = (unsigned char *)zalloc((size_t)n, 1);
    if (!state) return 0;
    state[0] = 2;
    for (v = 1; v < n; v++) {
        int u = v;
        while (state[u] == 0) { state[u] = 1; u = parents[u]; }
        if (state[u] == 1) { free(state); return 0; }
        u = v;
        while (state[u] == 1) { state[u] = 2; u = parents[u]; }
    }
    free(state);
    return 1;
}

void fdsm_destroy(void) {
    free(E); free(Epri); free(Eleaf); free(T); free(Tpri);
    free(croot); free(vcol); free(vpar); free(vch); free(fstack);
    free(alive); free(order); free(cntc); free(touched); free(stk); free(pre);
    E = NULL; Epri = NULL; Eleaf = NULL; T = NULL; Tpri = NULL;
    croot = vcol = vpar = vch = fstack = NULL;
    alive = NULL;
    order = cntc = touched = stk = pre = NULL;
    eroot = -1;
    nv = nC = cap = ftop = ready = order_changes = 0;
}

int fdsm_init(int n, int C, double alpha, int max_operations,
              const int *parents, const int *colors) {
    int *head = NULL, *next = NULL, *cursor = NULL, *seq = NULL, *off = NULL;
    int v, cur, m, c;
    if (!valid_input(n, C, alpha, max_operations, parents, colors)) return -1;
    fdsm_destroy();
    nC = C;
    nv = n;
    cap = n + max_operations + 4;
    rng = 0x9e3779b9u;
    ver = 1;
    E = zalloc((size_t)2 * cap, sizeof(*E));
    Epri = zalloc((size_t)2 * cap, sizeof(*Epri));
    Eleaf = zalloc((size_t)2 * cap, sizeof(*Eleaf));
    T = zalloc((size_t)cap, sizeof(*T));
    Tpri = zalloc((size_t)cap, sizeof(*Tpri));
    croot = zalloc((size_t)C, sizeof(*croot));
    vcol = zalloc((size_t)cap, sizeof(*vcol));
    vpar = zalloc((size_t)cap, sizeof(*vpar));
    vch = zalloc((size_t)cap, sizeof(*vch));
    fstack = zalloc((size_t)cap, sizeof(*fstack));
    alive = zalloc((size_t)cap, sizeof(*alive));
    order = zalloc((size_t)C, sizeof(*order));
    cntc = zalloc((size_t)C, sizeof(*cntc));
    touched = zalloc((size_t)C, sizeof(*touched));
    stk = zalloc((size_t)2 * cap, sizeof(*stk));
    pre = zalloc((size_t)2 * cap, sizeof(*pre));
    head = zalloc((size_t)n, sizeof(*head));
    next = zalloc((size_t)n, sizeof(*next));
    cursor = zalloc((size_t)n, sizeof(*cursor));
    seq = zalloc((size_t)2 * n, sizeof(*seq));
    off = zalloc((size_t)C + 1, sizeof(*off));
    if (!E || !Epri || !Eleaf || !T || !Tpri || !croot || !vcol || !vpar ||
        !vch || !fstack || !alive || !order || !cntc || !touched || !stk ||
        !pre || !head || !next || !cursor || !seq || !off) {
        free(head); free(next); free(cursor); free(seq); free(off);
        fdsm_destroy();
        return -1;
    }
    for (c = 0; c < C; c++) { croot[c] = -1; order[c] = c; }
    for (v = 0; v < n; v++) {
        vpar[v] = v ? parents[v] : -1;
        vcol[v] = colors[v];
        alive[v] = 1;
        head[v] = -1;
    }
    for (v = n - 1; v >= 1; v--) {
        int p = parents[v];
        next[v] = head[p];
        head[p] = v;
        vch[p]++;
    }
    memcpy(cursor, head, (size_t)n * sizeof(*cursor));

    /* Euler sequence by iterative DFS; children in increasing id order. */
    m = 0;
    cur = 0;
    enew(0, vch[0] == 0);
    seq[m++] = 0;
    while (cur >= 0) {
        int child = cursor[cur];
        if (child >= 0) {
            cursor[cur] = next[child];
            cur = child;
            enew(2 * cur, vch[cur] == 0);
            seq[m++] = 2 * cur;
        } else {
            enew(2 * cur + 1, 0);
            seq[m++] = 2 * cur + 1;
            cur = vpar[cur];
        }
    }
    eroot = ebuild(seq, m);

    /* Per color, its leaves in Euler order (counting sort). */
    for (v = 0; v < n; v++) if (!vch[v]) off[vcol[v] + 1]++;
    for (c = 0; c < C; c++) off[c + 1] += off[c];
    {
        int *fill = zalloc((size_t)C, sizeof(int)), i;
        if (!fill) {
            free(head); free(next); free(cursor); free(seq); free(off);
            fdsm_destroy();
            return -1;
        }
        memcpy(fill, off, (size_t)C * sizeof(int));
        for (i = 0; i < m; i++) {
            int e = seq[i];
            if (!(e & 1) && Eleaf[e]) {
                int u = e >> 1;
                tnew(u);
                head[fill[vcol[u]]++] = u;   /* reuse head[] as buffer */
            }
        }
        for (c = 0; c < C; c++)
            croot[c] = tbuild(head + off[c], off[c + 1] - off[c]);
        free(fill);
    }
    free(head); free(next); free(cursor); free(seq); free(off);
    order_changes = 1;
    ready = 1;
    return 0;
}

static int exists(int v) { return ready && v >= 0 && v < nv && alive[v]; }

int fdsm_update(int v, int color) {
    int pos;
    if (!exists(v) || color < 0 || color >= nC || vch[v] != 0) return -1;
    if (vcol[v] == color) return 0;
    pos = key_rank(v);
    tdelete(v, vcol[v]);
    vcol[v] = color;
    tinsert(color, v, pos);
    return 0;
}

int fdsm_query(int v, int *color, int *frequency) {
    int best_c = -1, best_f = 0, s, e, lps, lpe;
    if (!exists(v) || !color || !frequency) return -1;
    if (vch[v] == 0) { *color = vcol[v]; *frequency = 1; return 0; }
    s = erank_lp(2 * v, &lps);
    e = erank_lp(2 * v + 1, &lpe);
    if (e - s + 1 <= FDSM_SCAN_BASE + FDSM_SCAN_PER_COLOR * nC) {
        int x, nt = 0, i;
        for (x = enext(2 * v); x != 2 * v + 1; x = enext(x)) {
            if (Eleaf[x]) {
                int c = vcol[x >> 1];
                if (!cntc[c]++) touched[nt++] = c;
            }
        }
        for (i = 0; i < nt; i++) {
            int c = touched[i], k = cntc[c];
            if (k > best_f || (k == best_f && c < best_c)) { best_f = k; best_c = c; }
            cntc[c] = 0;
        }
    } else {
        int remaining = lpe - lps, i;
        sort_order();
        for (i = 0; i < nC; i++) {
            int c = order[i], t, k;
            if (croot[c] < 0) break;               /* all later colors empty */
            t = T[croot[c]].sz;
            if (t < best_f) break;                 /* sorted by total */
            if (t == best_f && c > best_c) continue;
            k = tcount(croot[c], s, e);
            if (k > best_f || (k == best_f && k > 0 && c < best_c)) {
                best_f = k; best_c = c;
            }
            remaining -= k;
            if (remaining < best_f) break;          /* nobody left can win */
        }
    }
    *frequency = best_f;
    *color = best_c;
    return 0;
}

int fdsm_add_leaf(int parent, int color) {
    int v, pos, a, b, pair;
    if (!exists(parent) || color < 0 || color >= nC) return -1;
    if (ftop) v = fstack[--ftop];
    else {
        if (nv >= cap) return -1;
        v = nv++;
    }
    if (vch[parent] == 0) {                 /* parent stops being a leaf */
        tdelete(parent, vcol[parent]);
        eset_leaf(2 * parent, 0);
    }
    pos = erank(2 * parent + 1);            /* v goes right before exit(parent) */
    tinsert(color, v, pos);                 /* compares in the old order */
    enew(2 * v, 1);
    enew(2 * v + 1, 0);
    pair = emerge(2 * v, 2 * v + 1);
    esplit(eroot, pos, &a, &b);
    eroot = emerge(emerge(a, pair), b);
    log_change(0, 0, 0, pos, 2);
    vpar[v] = parent;
    vch[v] = 0;
    vcol[v] = color;
    alive[v] = 1;
    vch[parent]++;
    return v;
}

int fdsm_remove_leaf(int v) {
    int p, q;
    if (!exists(v) || v == 0 || vch[v] != 0) return -1;
    p = vpar[v];
    q = key_rank(v);                         /* position of entry token 2v */
    tdelete(v, vcol[v]);
    if (vch[p] == 1)                         /* p becomes a leaf */
        tinsert(vcol[p], p, erank(2 * p));   /* compares in the old order */
    edelete(2 * v + 1);
    edelete(2 * v);
    log_change(1, 0, 0, q, 2);
    if (vch[p] == 1) eset_leaf(2 * p, 1);
    vch[p]--;
    alive[v] = 0;
    vpar[v] = -1;
    fstack[ftop++] = v;
    return 0;
}

/* Move the keys of color c in [from, until] to just before position pp
   (all positions in the current Euler order); returns how many moved. */
static int move_color(int c, int from, int until, int pp) {
    int X, R, Y, Z, A, B, ys;
    tsplit(croot[c], from, &X, &R);
    tsplit(R, until + 1, &Y, &Z);
    if (Y < 0) { croot[c] = tmerge(X, Z); return 0; }
    ys = T[Y].sz;
    if (pp < from) {
        tsplit(X, pp, &A, &B);
        croot[c] = tmerge(tmerge(A, Y), tmerge(B, Z));
    } else {
        tsplit(Z, pp, &A, &B);
        croot[c] = tmerge(tmerge(X, A), tmerge(Y, B));
    }
    return ys;
}

int fdsm_move(int v, int parent) {
    int op, from, until, lps, lpe, chk, leaves, pp, blk, i;
    if (!exists(v) || v == 0 || !exists(parent)) return -1;
    op = vpar[v];
    if (op == parent) return 0;
    from = erank_lp(2 * v, &lps);
    until = erank_lp(2 * v + 1, &lpe);
    chk = erank(2 * parent);
    if (from <= chk && chk <= until) return -1;   /* parent inside subtree */
    leaves = lpe - lps;                             /* leaves in subtree of v */
    blk = until - from + 1;

    if (vch[parent] == 0) {                 /* parent stops being a leaf */
        tdelete(parent, vcol[parent]);
        eset_leaf(2 * parent, 0);
    }
    pp = erank(2 * parent + 1);             /* block goes right before it */

    /* Phase 1: reorder the affected color trees, in the current order. */
    if (blk <= FDSM_SCAN_BASE + FDSM_SCAN_PER_COLOR * nC) {
        int x, nt = 0;
        for (x = 2 * v; ; x = enext(x)) {
            if (Eleaf[x]) {
                int c = vcol[x >> 1];
                if (!cntc[c]++) touched[nt++] = c;
            }
            if (x == 2 * v + 1) break;
        }
        for (i = 0; i < nt; i++) {
            cntc[touched[i]] = 0;
            move_color(touched[i], from, until, pp);
        }
    } else {
        int moved = 0;
        sort_order();
        for (i = 0; i < nC && moved < leaves; i++) {
            int c = order[i];
            if (croot[c] < 0) break;
            if (tpresent(croot[c], from, until + 1))
                moved += move_color(c, from, until, pp);
        }
    }

    /* Phase 2: move the Euler block. */
    {
        int a, b, mid, d, ins = pp < from ? pp : pp - blk;
        esplit(eroot, from, &a, &b);
        esplit(b, blk, &mid, &d);
        eroot = emerge(a, d);
        esplit(eroot, ins, &a, &b);
        eroot = emerge(emerge(a, mid), b);
    }
    log_change(2, from, until, pp, 0);
    vpar[v] = parent;
    vch[op]--;
    vch[parent]++;
    if (vch[op] == 0) {                      /* old parent becomes a leaf */
        eset_leaf(2 * op, 1);
        tinsert(vcol[op], op, erank(2 * op));
    }
    return 0;
}
