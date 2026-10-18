/*
 * dsm.c -- Dynamic Subtree Mode (Theorem 1 of the paper), optimized.
 *
 * Public API:
 *   int  dsm_init(int n, int C, double alpha, const int *parents, const int *colors);
 *   int  dsm_update(int v, int color);
 *   int  dsm_query(int v, int *color, int *frequency);
 *   void dsm_destroy(void);
 * Ties go to the smallest color index.
 *
 * Structure (as in the paper): colors with at least n^(1-alpha) leaves are
 * heavy, the others light; every color keeps its single-color tree (the
 * LCA-closure of its leaves) with explicit parent pointers and a search tree
 * of its leaves in DFS order; every node keeps a search tree of the light
 * colors branching at it, ordered by frequency; the tree is cut into groups
 * ("decomposition subtrees") of size O(n^alpha), and every group root keeps
 * the best light entry of its region and of its child groups.
 *
 * Changes with respect to the previous implementation:
 *  1. A node with two or more group-root children is made a group root, so
 *     a query below a non-root node visits O(n^alpha) nodes (previously the
 *     walk could iterate over Theta(n/n^alpha) group roots).
 *  2. An update repairs only the group summaries that changed, deepest
 *     first (previously every group was scanned, Theta(n) time at alpha=0).
 *  3. Group roots keep, in a flat table, the number of leaves of every heavy
 *     color below them (O(n) ints in total); a query at a group root reads
 *     its row, and a query at another node combines the counts of its region
 *     with the rows of its (few) group-root children.  Heavy colors therefore
 *     need no link-cut trees; the link-cut trees were removed altogether, the
 *     node to re-attach when a single-color tree gains a branching node is
 *     found with two search-tree lookups and one LCA query instead.
 *  4. Subtrees with few leaves are answered by scanning their leaves, which
 *     are stored contiguously in pre-order.
 *  5. The light walk of a query reads a pre-order array (16 bytes per node)
 *     instead of chasing adjacency lists; it is iterative (the old recursion
 *     overflowed the stack on deep trees at large alpha).
 *  6. The per-node light trees and the per-group summaries are repaired
 *     with value changes that stop as soon as a maximum is unchanged, instead
 *     of delete+insert pairs; a leaf no longer carries a one-node map.
 *  7. Construction-only arrays are released after construction.
 * All bounds of Theorem 1 are kept; alpha = 0 realizes Theorem 2 (O~(h)
 * updates), since an update only touches ancestors.
 *
 * Tuning (compile-time): DSM_SCAN_BASE + DSM_SCAN_PER_HEAVY * (#heavy colors)
 * leaves or fewer are scanned directly; DSM_DR_CAP group-root children at
 * most are combined by table lookups, more fall back to rank queries.
 */
int dsm_init(int n, int C, double alpha, const int *parents, const int *colors);
int dsm_update(int v, int color);
int dsm_query(int v, int *color, int *frequency);
void dsm_destroy(void);

static int api_ready;

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stddef.h>
#include <limits.h>

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

static int capped_mul_add_int(int n, int mult, int add) {
    long long raw = (long long)n * (long long)mult + (long long)add;
    if (raw > (long long)INT_MAX - 1LL) return INT_MAX - 1;
    return (int)raw;
}

static long long MC;
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

static int tpv(int r, int k) {
    int s = -1;
    while (r) {
        if (_tp[r].k < k) {
            s = (int)_tp[r].mv;
            r = _tp[r].r;
        } else {
            r = _tp[r].l;
        }
    }
    return s;
}

static int tfindv(int r, int k) {
    while (r) {
        if (k == _tp[r].k) return (int)_tp[r].mv;
        r = (k < _tp[r].k) ? _tp[r].l : _tp[r].r;
    }
    return 0;
}

static int tsv(int r, int k) {
    int s = -1;
    while (r) {
        if (_tp[r].k > k) {
            s = (int)_tp[r].mv;
            r = _tp[r].l;
        } else {
            r = _tp[r].r;
        }
    }
    return s;
}

static int *_cb;
static int _cc;

static void tco(int t) {
    if (!t) return;
    tco(_tp[t].l);
    _cb[_cc++] = (int)_tp[t].mv;
    tco(_tp[t].r);
}

static int tbd_rec(int *ks, long long *vs, int l, int r) {
    int m, nd;
    if (l > r) return 0;
    m = (l + r) >> 1;
    nd = ta(ks[m], vs[m]);
    _tp[nd].l = tbd_rec(ks, vs, l, m - 1);
    _tp[nd].r = tbd_rec(ks, vs, m + 1, r);
    tpu(nd);
    return nd;
}

static int tbd(int *ks, long long *vs, int n) {
    if (!n) return 0;

    tensure(_tn + n);
    return tbd_rec(ks, vs, 0, n - 1);
}

typedef struct AN {
    int k, h;
    int l, r;
    long long mv, mx;
} AN;

static AN *_atp;
static int _atp_cap;
static int _atp_cap_max;
static int _atn;
static int _afl;

static void aensure(int need) {
    int nc = _atp_cap;
    if (need < _atp_cap) return;
    while (nc <= need && nc < _atp_cap_max) {
        int nxt = nc << 1;
        if (nxt <= nc) {
            nc = _atp_cap_max;
            break;
        }
        if (nxt > _atp_cap_max) nxt = _atp_cap_max;
        nc = nxt;
    }
    if (need >= nc) {
        fprintf(stderr, "ATPOOL\n");
        exit(1);
    }
    _atp = (AN *)xrealloc(_atp, (size_t)nc * sizeof(AN));
    _atp_cap = nc;
}

static int aa(int k, long long v) {
    int x;
    AN *t;
    if (_afl) {
        x = _afl;
        _afl = _atp[x].r;
    } else {
        aensure(_atn);
        x = _atn++;
    }
    t = &_atp[x];
    t->k = k;
    t->h = 1;
    t->l = 0;
    t->r = 0;
    t->mv = v;
    t->mx = v;
    return x;
}

static int aht(int x) { return x ? _atp[x].h : 0; }

static void apu(int x) {
    AN *t;
    if (!x) return;
    t = &_atp[x];
    t->h = 1 + (aht(t->l) > aht(t->r) ? aht(t->l) : aht(t->r));
    t->mx = t->mv;
    if (t->l && _atp[t->l].mx > t->mx) t->mx = _atp[t->l].mx;
    if (t->r && _atp[t->r].mx > t->mx) t->mx = _atp[t->r].mx;
}

static int abd_rec(int *ks, long long *vs, int l, int r) {
    int m, nd;
    if (l > r) return 0;
    m = (l + r) >> 1;
    nd = aa(ks[m], vs[m]);
    _atp[nd].l = abd_rec(ks, vs, l, m - 1);
    _atp[nd].r = abd_rec(ks, vs, m + 1, r);
    apu(nd);
    return nd;
}

static int abd(int *ks, long long *vs, int n) {
    if (!n) return 0;

    aensure(_atn + n);
    return abd_rec(ks, vs, 0, n - 1);
}

/* Change the value of key k (which must be present) and repair the max
   augmentation along the search path; stops as soon as a max is unchanged. */
static int _a_stk[128];
static void achg(int r, int k, long long v) {
    int sp = 0, x = r;
    while (x) {
        _a_stk[sp++] = x;
        if (k == _atp[x].k) break;
        x = (k < _atp[x].k) ? _atp[x].l : _atp[x].r;
    }
    if (!x) return;
    _atp[x].mv = v;
    while (sp > 0) {
        AN *t;
        long long m;
        x = _a_stk[--sp];
        t = &_atp[x];
        m = t->mv;
        if (t->l && _atp[t->l].mx > m) m = _atp[t->l].mx;
        if (t->r && _atp[t->r].mx > m) m = _atp[t->r].mx;
        if (t->mx == m) break;
        t->mx = m;
    }
}

static int *dep;
static struct {
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
    return x;
}

static void pf2(int x) {
    if (!x) return;
    P[x].tc[1] = pfr_;
    pfr_ = x;
}

static int lht(int x) { return x ? P[x].th : 0; }

static void lpu(int x) {
    if (!x) return;
    P[x].th = 1 + (lht(P[x].tc[0]) > lht(P[x].tc[1]) ? lht(P[x].tc[0]) : lht(P[x].tc[1]));
    P[x].tmx = menc(P[x].cnt, P[x].c);
    if (P[x].tc[0]) {
        if (P[P[x].tc[0]].tmx > P[x].tmx) P[x].tmx = P[P[x].tc[0]].tmx;
    }
    if (P[x].tc[1]) {
        if (P[P[x].tc[1]].tmx > P[x].tmx) P[x].tmx = P[P[x].tc[1]].tmx;
    }
}

static int lrrot2(int y) {
    int x = P[y].tc[0], z = P[x].tc[1];
    P[x].tc[1] = y;
    P[y].tc[0] = z;
    lpu(y);
    lpu(x);
    return x;
}

static int llrot2(int x) {
    int y = P[x].tc[1], z = P[y].tc[0];
    P[y].tc[0] = x;
    P[x].tc[1] = z;
    lpu(x);
    lpu(y);
    return y;
}

static int lbal(int x) {
    int bf;
    if (!x) return 0;
    bf = lht(P[x].tc[0]) - lht(P[x].tc[1]);
    if (bf > 1) {
        if (lht(P[P[x].tc[0]].tc[0]) < lht(P[P[x].tc[0]].tc[1])) P[x].tc[0] = llrot2(P[x].tc[0]);
        return lrrot2(x);
    }
    if (bf < -1) {
        if (lht(P[P[x].tc[1]].tc[1]) < lht(P[P[x].tc[1]].tc[0])) P[x].tc[1] = lrrot2(P[x].tc[1]);
        return llrot2(x);
    }
    return x;
}

static int lins1(int root, int x) {
    if (!root) return x;
    if (P[x].c < P[root].c) P[root].tc[0] = lins1(P[root].tc[0], x);
    else if (P[x].c > P[root].c) P[root].tc[1] = lins1(P[root].tc[1], x);
    else {
        P[root].cnt = P[x].cnt;
        pf2(x);
        lpu(root);
        return root;
    }
    lpu(root);
    return lbal(root);
}

static void lins(int *root, int x) {
    P[x].tc[0] = 0;
    P[x].tc[1] = 0;
    P[x].th = 1;
    P[x].tmx = menc(P[x].cnt, P[x].c);
    *root = lins1(*root, x);
}

static int ltake_min(int root, int *mn) {
    if (!P[root].tc[0]) {
        *mn = root;
        return P[root].tc[1];
    }
    P[root].tc[0] = ltake_min(P[root].tc[0], mn);
    lpu(root);
    return lbal(root);
}

static int lex1(int root, int k, int *out) {
    if (!root) return 0;
    if (k < P[root].c) P[root].tc[0] = lex1(P[root].tc[0], k, out);
    else if (k > P[root].c) P[root].tc[1] = lex1(P[root].tc[1], k, out);
    else {
        *out = root;
        if (!P[root].tc[0]) return P[root].tc[1];
        if (!P[root].tc[1]) return P[root].tc[0];
        {
            int rep = 0;
            int nr = ltake_min(P[root].tc[1], &rep);
            P[rep].tc[0] = P[root].tc[0];
            P[rep].tc[1] = nr;
            lpu(rep);
            return lbal(rep);
        }
    }
    lpu(root);
    return lbal(root);
}

static int lex(int *root, int k) {
    int out = 0;
    *root = lex1(*root, k, &out);
    if (out) {
        P[out].tc[0] = 0;
        P[out].tc[1] = 0;
        P[out].th = 1;
        P[out].tmx = menc(P[out].cnt, P[out].c);
    }
    return out;
}

static int *_lt_stk;
/* Set the count of color c in the light tree rooted at root and repair the
   max augmentation along the search path; heights are unchanged, and the
   repair stops at the first node whose max did not change. */
static void lt_adj(int root, int c, long long nv) {
    int sp = 0, t = root;
    while (t) {
        _lt_stk[sp++] = t;
        if (P[t].c == c) break;
        t = (c < P[t].c) ? P[t].tc[0] : P[t].tc[1];
    }
    if (!t) return;
    P[t].cnt = mf(nv);
    while (sp > 0) {
        int x = _lt_stk[--sp];
        long long m = menc(P[x].cnt, P[x].c);
        if (P[x].tc[0] && P[P[x].tc[0]].tmx > m) m = P[P[x].tc[0]].tmx;
        if (P[x].tc[1] && P[P[x].tc[1]].tmx > m) m = P[P[x].tc[1]].tmx;
        if (P[x].tmx == m) break;
        P[x].tmx = m;
    }
}

static int lt_bld_rec(int *arr, int l, int r) {
    int m, x;
    if (l > r) return 0;
    m = (l + r) >> 1;
    x = arr[m];
    P[x].tc[0] = lt_bld_rec(arr, l, m - 1);
    P[x].tc[1] = lt_bld_rec(arr, m + 1, r);
    lpu(x);
    return x;
}

static int lt_bld(int *arr, int n) {
    if (!n) return 0;
    return lt_bld_rec(arr, 0, n - 1);
}

static void rt_link(int x, int y) {
    P[x].par = y;
    P[x].nsb = P[y].fch;
    P[x].prv = 0;
    if (P[y].fch) P[P[y].fch].prv = x;
    P[y].fch = x;
}

static void rt_cut(int x) {
    int y = P[x].par;
    if (!y) return;
    if (P[x].prv) P[P[x].prv].nsb = P[x].nsb;
    else P[y].fch = P[x].nsb;
    if (P[x].nsb) P[P[x].nsb].prv = P[x].prv;
    P[x].par = 0;
    P[x].nsb = 0;
    P[x].prv = 0;
}

static int *LR;

static int N, Q, nC;
static double alp;
static int *hd, *nx, *to, ec;
static int *pa, *tin, *tout, tmr_;
static int *tinv;
static int *il, *col;
static int *dlv, ndl;
static int *pre, *sz_, *lidx, *nlv, *lpos, *lcol;   /* pre-order index, subtree size, leaf range, leaf colors in pre-order */
static int *lst, *lcnt, lstamp;                     /* stamped counters for leaf scans */
static int *gpos, *hq, hn;                          /* BFS position of a group; heap of affected groups */
typedef struct { long long tmx; int grp, sz, lc, pad_; } TT;  /* per pre-order position: light max, group if DR root (else -1), subtree size, leaf color (-1 if internal) */
static TT *tt;
#ifndef DSM_SCAN_BASE
#define DSM_SCAN_BASE 64
#endif
#ifndef DSM_SCAN_PER_HEAVY
#define DSM_SCAN_PER_HEAVY 4
#endif
static int *es, *ed, *ef, eln;

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
    int sp = 0, pc = 0;
    _ds[0] = 0;
    _di[0] = hd[0];
    pa[0] = -1;
    dep[0] = 0;
    pre[0] = pc++;
    tin[0] = tmr_++;
    tinv[tin[0]] = 0;
    ef[0] = eln;
    es[eln] = 0;
    ed[eln] = 0;
    eln++;
    while (sp >= 0) {
        int u = _ds[sp];
        if (_di[sp] != -1) {
            int e = _di[sp];
            int v;
            _di[sp] = nx[e];
            v = to[e];
            if (v == pa[u]) continue;
            pa[v] = u;
            dep[v] = dep[u] + 1;
            sp++;
            _ds[sp] = v;
            _di[sp] = hd[v];
            pre[v] = pc++;
            tin[v] = tmr_++;
            tinv[tin[v]] = v;
            ef[v] = eln;
            es[eln] = v;
            ed[eln] = dep[v];
            eln++;
        } else {
            int leaf = 1, e;
            for (e = hd[u]; e != -1; e = nx[e]) {
                if (to[e] != pa[u]) {
                    leaf = 0;
                    break;
                }
            }
            il[u] = leaf;
            if (leaf) { lpos[u] = ndl; dlv[ndl++] = u; }
            sz_[u] = pc - pre[u];
            tout[u] = tmr_++;
            sp--;
            if (sp >= 0) {
                int p2 = _ds[sp];
                es[eln] = p2;
                ed[eln] = dep[p2];
                eln++;
            }
        }
    }
}

#define MBS 14
#define MBT (1 << MBS)
static int rb, rn;
static int *rbm, *rbt, *rsp, *rlg, rsp_levels;
static signed char rlu[MBT][MBS][MBS];
static char rlo[MBT];

#define RSP(level, idx) rsp[(size_t)(level) * (size_t)rn + (size_t)(idx)]

static void rmq_build(void) {
    int m = eln, b, j, i;
    if (m <= 1) {
        rb = 1;
        rn = m;
    } else {
        int lg = 1;
        while ((1 << lg) < m) lg++;
        rb = lg / 2;
        if (rb < 1) rb = 1;
        if (rb > MBS) rb = MBS;
        rn = (m + rb - 1) / rb;
    }
    rbm = (int *)xmalloc((size_t)(rn > 0 ? rn : 1) * sizeof(int));
    rbt = (int *)xmalloc((size_t)(rn > 0 ? rn : 1) * sizeof(int));
    rlg = (int *)xmalloc((size_t)(rn + 2) * sizeof(int));
    memset(rlo, 0, sizeof(rlo));
    for (b = 0; b < rn; b++) {
        int s = b * rb, e2 = s + rb, bl, tp = 0, mi;
        if (e2 > m) e2 = m;
        bl = e2 - s;
        for (i = 0; i < bl - 1; i++) if (ed[s + i + 1] > ed[s + i]) tp |= (1 << i);
        rbt[b] = tp;
        if (!rlo[tp]) {
            int v2[MBS];
            rlo[tp] = 1;
            v2[0] = 0;
            for (i = 0; i < rb - 1; i++) v2[i + 1] = v2[i] + ((tp & (1 << i)) ? 1 : -1);
            for (i = 0; i < rb; i++) {
                rlu[tp][i][i] = (signed char)i;
                for (j = i + 1; j < rb; j++) {
                    rlu[tp][i][j] =
                        (v2[j] < v2[(int)(unsigned char)rlu[tp][i][j - 1]]) ? (signed char)j : rlu[tp][i][j - 1];
                }
            }
        }
        mi = s;
        for (i = s + 1; i < e2; i++) if (ed[i] < ed[mi]) mi = i;
        rbm[b] = mi;
    }
    if (rn >= 1) rlg[1] = 0;
    for (i = 2; i <= rn; i++) rlg[i] = rlg[i / 2] + 1;
    rsp_levels = (rn >= 1) ? (rlg[rn] + 1) : 1;
    rsp = (int *)xmalloc((size_t)rsp_levels * (size_t)(rn > 0 ? rn : 1) * sizeof(int));
    for (b = 0; b < rn; b++) RSP(0, b) = b;
    for (j = 1; (1 << j) <= rn; j++) {
        for (i = 0; i + (1 << j) <= rn; i++) {
            int a = RSP(j - 1, i), b2 = RSP(j - 1, i + (1 << (j - 1)));
            RSP(j, i) = (ed[rbm[a]] <= ed[rbm[b2]]) ? a : b2;
        }
    }
}

static int rmq(int l, int r) {
    int bl = l / rb, br = r / rb;
    if (bl == br) return bl * rb + rlu[rbt[bl]][l - bl * rb][r - bl * rb];
    {
        int i1 = bl * rb + rlu[rbt[bl]][l - bl * rb][(bl + 1) * rb - 1 - bl * rb];
        int i2 = br * rb + rlu[rbt[br]][0][r - br * rb];
        int best = (ed[i1] <= ed[i2]) ? i1 : i2;
        if (bl + 1 < br) {
            int k = rlg[br - bl - 1];
            int a = RSP(k, bl + 1), b2 = RSP(k, br - (1 << k));
            int mb = (ed[rbm[a]] <= ed[rbm[b2]]) ? a : b2;
            if (ed[rbm[mb]] < ed[best]) best = rbm[mb];
        }
        return best;
    }
}

static int lca(int u, int v) {
    int l = ef[u], r = ef[v];
    if (l > r) {
        int t = l;
        l = r;
        r = t;
    }
    return es[rmq(l, r)];
}

static int B_sz, thr, *gid, *groot, nG, *isDR, *drp;
static int *dh_to, *dh_nx, *dh_hd, dh_ec;
static int *gq, gqn;
static int *_dw, *_dq;

static void decompose(void) {
    int poc = 0, sp, i, g;
    sp = 0;
    _ds[0] = 0;
    _di[0] = hd[0];
    while (sp >= 0) {
        int u = _ds[sp], f = 0;
        while (_di[sp] != -1) {
            int e = _di[sp], v;
            _di[sp] = nx[e];
            v = to[e];
            if (v == pa[u]) continue;
            sp++;
            _ds[sp] = v;
            _di[sp] = hd[v];
            f = 1;
            break;
        }
        if (!f) {
            _dq[poc++] = u;
            sp--;
        }
    }

    memset(isDR, 0, N * sizeof(int));
    for (i = 0; i < poc; i++) {
        int u = _dq[i], e;
        int drc = 0;
        _dw[u] = 1;
        for (e = hd[u]; e != -1; e = nx[e]) {
            int v = to[e];
            if (v == pa[u]) continue;
            if (!isDR[v]) _dw[u] += _dw[v];
            else drc++;
        }
        /* a node with two or more DR children is made DR as well, so that every
           non-DR node has at most one DR child and a query walk below a non-DR
           node costs O(B_sz) (the number of DR nodes at most doubles) */
        if (_dw[u] >= B_sz || u == 0 || drc >= 2) isDR[u] = 1;
    }

    nG = 0;
    gid[0] = nG;
    groot[nG] = 0;
    nG++;
    {
        int qh = 0, qt = 0;
        _dq[qt++] = 0;
        while (qh < qt) {
            int u = _dq[qh++], e;
            for (e = hd[u]; e != -1; e = nx[e]) {
                int v = to[e];
                if (v == pa[u]) continue;
                if (isDR[v]) {
                    gid[v] = nG;
                    groot[nG] = v;
                    nG++;
                } else gid[v] = gid[u];
                _dq[qt++] = v;
            }
        }
    }

    for (g = 0; g < nG; g++) {
        int r = groot[g];
        drp[g] = (r == 0) ? -1 : gid[pa[r]];
    }

    dh_ec = 0;
    memset(dh_hd, -1, nG * sizeof(int));
    for (g = nG - 1; g >= 0; g--) {
        if (drp[g] >= 0) {
            dh_to[dh_ec] = g;
            dh_nx[dh_ec] = dh_hd[drp[g]];
            dh_hd[drp[g]] = dh_ec++;
        }
    }

    gqn = 0;
    {
        int qh = 0;
        gq[gqn++] = 0;
        while (qh < gqn) {
            int gg = gq[qh++], e;
            for (e = dh_hd[gg]; e != -1; e = dh_nx[e]) gq[gqn++] = dh_to[e];
        }
    }
    for (i = 0; i < gqn; i++) gpos[gq[i]] = i;
    for (i = 0; i < N; i++) {
        tt[pre[i]].grp = isDR[i] ? gid[i] : -1;
        tt[pre[i]].sz = sz_[i];
        tt[pre[i]].tmx = -1;
        tt[pre[i]].lc = il[i] ? col[i] : -1;
        tt[pre[i]].pad_ = 0;
    }
}

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
            int a = lca(v, _vs[sp - 1]);
            while (sp >= 2 && dep[_vs[sp - 2]] >= dep[a]) {
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

static int *freq, *isH, *hvl, nHv;
/* Heavy-color counts at group roots: hct[g * hcap + j] is the number of leaves
   of heavy color hvl[j] below the root of group g; hidx[c] is the column of
   color c, -1 if c is light.  nG * hcap = O(n). */
static int *hct, *hidx, hcap;
#ifndef DSM_DR_CAP
#define DSM_DR_CAP 16
#endif
static int *cL;
static int *cT;
static int *AP_;
static int *la_, *dcc_;
static long long *lm;
static int *afg_, naf_, *afv_, afgen_;

static int fvc(int w, int c) { return tcrng(cL[c], tin[w], tout[w] - 1); }

static void maf(int w);
static void upd_la(int w) {
    long long nv = LR[w] ? P[LR[w]].tmx : -1;
    TT *t = &tt[pre[w]];
    if (t->tmx == nv) return;
    t->tmx = nv;
    achg(la_[gid[w]], w, nv);
    maf(w);
}

static void rlm(int g) {
    long long b = -1;
    if (la_[g] && _atp[la_[g]].mx > b) b = _atp[la_[g]].mx;
    if (dcc_[g] && _atp[dcc_[g]].mx > b) b = _atp[dcc_[g]].mx;
    lm[g] = b;
}

static void maf(int w) {
    int g = gid[w];
    if (afv_[g] != afgen_) {
        afv_[g] = afgen_;
        afg_[naf_++] = g;
    }
}

static int is_st(int c, int w) { return !(il[w] && col[w] == c); }

/* The single-color-tree node of color c at vertex w: a leaf has at most one
   such node (for its own color), kept in lfx; internal vertices use AP_. */
static int *lfx;
static int ap_find(int w, int c) { return il[w] ? ((col[w] == c) ? lfx[w] : 0) : tfindv(AP_[w], c); }
static void ap_ins(int w, int c, int x) { if (il[w]) lfx[w] = x; else tins(&AP_[w], c, x); }
static void ap_del(int w, int c) { if (il[w]) lfx[w] = 0; else tdel(&AP_[w], c); }

/* Add delta to the count of a light color at x and at all its ancestors in
   the single-color tree, following the explicit parent pointers (no lazy
   values are ever pending: heavy colors keep no counts in these trees). */
static void anc_adj_prop_light(int x, int delta) {
    int nd;
    for (nd = x; nd; nd = P[nd].par) {
        P[nd].cnt += delta;
        lt_adj(LR[P[nd].w], P[nd].c, menc(P[nd].cnt, P[nd].c));
        upd_la(P[nd].w);
    }
}

static void anc_adj_prop(int x, int c, int delta) {
    if (!x) return;
    if (!isH[c]) anc_adj_prop_light(x, delta);
}

/* add delta to the count of heavy column j at every DR ancestor of leaf v */
static void hct_path_add(int v, int j, int delta) {
    int g = gid[v];
    while (g >= 0) {
        hct[(size_t)g * hcap + j] += delta;
        g = drp[g];
    }
}

/* column j of a color that just became heavy: counts at every group root */
static void hct_fill_column(int c, int j) {
    int g;
    for (g = 0; g < nG; g++) hct[(size_t)g * hcap + j] = fvc(groot[g], c);
}

/* remove column j (color becomes light): move the last column into it */
static void hct_drop_column(int j) {
    int g, last = nHv - 1;
    if (j != last) {
        for (g = 0; g < nG; g++) hct[(size_t)g * hcap + j] = hct[(size_t)g * hcap + last];
        hvl[j] = hvl[last];
        hidx[hvl[j]] = j;
    }
    nHv--;
}

static void light_rem_full(int c) {
    int i;
    if (!cL[c]) return;
    comp_tc(cL[c]);
    for (i = 0; i < tcn; i++) {
        int w = tcb[i];
        (void)lex(&LR[w], c);
        upd_la(w);
    }
}

static void light_add_full(int c) {
    int i;
    if (!cL[c]) return;
    comp_tc(cL[c]);
    for (i = 0; i < tcn; i++) {
        int w = tcb[i];
        int x = ap_find(w, c);
        if (!x) continue;
        P[x].cnt = fvc(w, c);
        lins(&LR[w], x);
        upd_la(w);
    }
}

static void st_rem(int v, int c) {
    int vx = ap_find(v, c);
    if (!vx) return;
    {
        int par = P[vx].par;
        rt_cut(vx);
        ap_del(v, c);
        if (!isH[c]) {
            (void)lex(&LR[v], c);
            upd_la(v);
        }
        if (par) anc_adj_prop(par, c, -1);
        if (par) {
            int pw;
            P[par].sd--;
            pw = P[par].w;
            if (P[par].sd == 1 && is_st(c, pw)) {
                int ch = P[par].fch;
                int pp = P[par].par;
                rt_cut(ch);
                rt_cut(par);
                if (pp) rt_link(ch, pp);
                ap_del(pw, c);
                if (!isH[c]) {
                    (void)lex(&LR[pw], c);
                    upd_la(pw);
                }
                pf2(par);
            } else if (P[par].sd == 0 && is_st(c, pw)) {
                rt_cut(par);
                ap_del(pw, c);
                if (!isH[c]) {
                    (void)lex(&LR[pw], c);
                    upd_la(pw);
                }
                pf2(par);
            }
        }
    }
    pf2(vx);
}

static void st_add(int v, int c) {
    int sz = tsz(cL[c]);
    if (sz <= 0) return;
    if (sz == 1) {
        int x = pa2(v, c, 1);
        P[x].sd = 0;
        ap_ins(v, c, x);
        if (!isH[c]) {
            lins(&LR[v], x);
            upd_la(v);
        }
        return;
    }
    if (sz == 2) {
        int pn = tpv(cL[c], tin[v]), sn = tsv(cL[c], tin[v]);
        int other = (pn >= 0) ? pn : sn;
        int ox = ap_find(other, c);
        int vp = lca(other, v);
        int vx = pa2(v, c, 1);
        int vpx = pa2(vp, c, 2);
        P[vx].sd = 0;
        P[vpx].sd = 2;
        ap_ins(v, c, vx);
        ap_ins(vp, c, vpx);
        if (!isH[c]) {
            lins(&LR[v], vx);
            upd_la(v);
            lins(&LR[vp], vpx);
            upd_la(vp);
        }
        rt_cut(ox);
        rt_link(ox, vpx);
        rt_link(vx, vpx);
        return;
    }

    {
        int pn = tpv(cL[c], tin[v]), sn = tsv(cL[c], tin[v]);
        int a1 = (pn >= 0) ? lca(pn, v) : -1;
        int a2 = (sn >= 0) ? lca(v, sn) : -1;
        int vp, px, vx;

        if (a1 >= 0 && a2 >= 0) vp = (dep[a1] >= dep[a2]) ? a1 : a2;
        else if (a1 >= 0) vp = a1;
        else vp = a2;

        px = ap_find(vp, c);
        vx = pa2(v, c, 1);
        P[vx].sd = 0;
        ap_ins(v, c, vx);
        if (!isH[c]) {
            lins(&LR[v], vx);
            upd_la(v);
        }

        if (px) {
            rt_link(vx, px);
            P[px].sd++;
            anc_adj_prop(px, c, 1);
        } else {
            int nbr = (a1 >= 0 && a2 >= 0) ? ((dep[a1] >= dep[a2]) ? pn : sn) : ((pn >= 0) ? pn : sn);
            int ox = ap_find(nbr, c);
            if (!ox) {
                ap_del(v, c);
                if (!isH[c]) {
                    (void)lex(&LR[v], c);
                    upd_la(v);
                }
                pf2(vx);
                return;
            }
            {
                int xi, yi, vpc, vpx, f, l, lw;
                /* vp is not in T_c, so the c-leaves below vp other than v all lie
                   in one child subtree of vp, on nbr's side of v; the topmost
                   T_c node there is the LCA of the first and last of them */
                if (nbr == pn) {
                    f = tsv(cL[c], tin[vp] - 1);
                    l = pn;
                } else {
                    f = sn;
                    l = tpv(cL[c], tout[vp]);
                }
                lw = (f == l) ? f : lca(f, l);
                xi = ap_find(lw, c);
                if (!xi) {
                    ap_del(v, c);
                    if (!isH[c]) {
                        (void)lex(&LR[v], c);
                        upd_la(v);
                    }
                    pf2(vx);
                    return;
                }
                yi = P[xi].par;
                vpc = fvc(vp, c);
                vpx = pa2(vp, c, vpc);
                P[vpx].sd = 2;
                ap_ins(vp, c, vpx);
                if (!isH[c]) {
                    lins(&LR[vp], vpx);
                    upd_la(vp);
                }
                rt_cut(xi);
                rt_link(xi, vpx);
                rt_link(vx, vpx);
                if (yi) rt_link(vpx, yi);
                if (yi) anc_adj_prop(yi, c, 1);
            }
        }
    }
}

static void dsm_build(void) {
    int v, c, w, i;
    int nxt_cap;
    int *bk = (int *)xmalloc((size_t)N * 3 * sizeof(int));
    long long *bv = (long long *)xmalloc((size_t)N * 3 * sizeof(long long));
    int *bc = (int *)xcalloc((size_t)nC, sizeof(int));
    int *bo = (int *)xmalloc((size_t)nC * sizeof(int));
    int *bt = (int *)xcalloc((size_t)nC, sizeof(int));
    int *ar_head = (int *)xcalloc((size_t)N, sizeof(int));
    int *ar_nxt;
    int *lr_head = (int *)xcalloc((size_t)N, sizeof(int));
    int *lr_nxt;
    int *ltb = (int *)xmalloc((size_t)N * sizeof(int));
    int *apb = (int *)xmalloc((size_t)N * sizeof(int));
    int *mp2 = (int *)xmalloc((size_t)N * sizeof(int));
    nxt_cap = _p_cap;
    ar_nxt = (int *)xmalloc((size_t)nxt_cap * sizeof(int));
    lr_nxt = (int *)xmalloc((size_t)nxt_cap * sizeof(int));
    B_sz = (int)ceil(pow(N, alp));
    if (B_sz < 1) B_sz = 1;
    thr = (int)ceil(pow(N, 1.0 - alp));
    if (thr < 1) thr = 1;

    memset(freq, 0, nC * sizeof(int));
    for (v = 0; v < N; v++) if (il[v] && col[v] >= 0 && col[v] < nC) freq[col[v]]++;
    nHv = 0;
    memset(isH, 0, nC * sizeof(int));
    for (c = 0; c < nC; c++) {
        hidx[c] = -1;
        if (freq[c] >= thr) {
            isH[c] = 1;
            hidx[c] = nHv;
            hvl[nHv++] = c;
        }
    }
    decompose();
    /* the adjacency lists, DFS stacks, and inverse DFS numbering are no longer needed */
    free(hd); free(nx); free(to); free(tinv); free(_dw); free(_dq); free(_ds); free(_di); free(pa);
    hd = nx = to = tinv = _dw = _dq = _ds = _di = pa = NULL;
    hcap = (ndl / thr) + 2;
    if (hcap < nHv) hcap = nHv;
    hct = (int *)xcalloc((size_t)nG * (size_t)hcap, sizeof(int));
    for (i = 0; i < ndl; i++) {
        int j = hidx[col[dlv[i]]];
        if (j >= 0) hct[(size_t)gid[dlv[i]] * hcap + j]++;
    }
    for (i = gqn - 1; i > 0; i--) {
        int g = gq[i], pg = drp[g], j;
        int *src = hct + (size_t)g * hcap, *dst = hct + (size_t)pg * hcap;
        for (j = 0; j < nHv; j++) dst[j] += src[j];
    }

    memset(cL, 0, (size_t)nC * sizeof(int));
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
        bk[idx] = tin[vv];
        bv[idx] = (long long)vv;
    }
    for (c = 0; c < nC; c++) if (bc[c] > 0) cL[c] = tbd(bk + bo[c], bv + bo[c], bc[c]);

    for (w = 0; w < N; w++) {
        LR[w] = 0;
        AP_[w] = 0;
    }

    for (c = nC - 1; c >= 0; c--) {
        if (!cL[c]) continue;
        comp_tc(cL[c]);
        for (i = 0; i < tcn; i++) {
            int x;
            w = tcb[i];
            x = pa2(w, c, tcf[i]);
            if (x >= nxt_cap) {
                int nc = nxt_cap;
                while (nc <= x && nc < _p_cap_max) {
                    int next = (nc > _p_cap_max / 2) ? _p_cap_max : (nc << 1);
                    if (next <= nc) next = _p_cap_max;
                    nc = next;
                }
                if (x >= nc) {
                    fprintf(stderr, "AUXNXT capacity exhausted: need=%d max=%d\n",
                            x, _p_cap_max);
                    exit(1);
                }
                ar_nxt = (int *)xrealloc(ar_nxt, (size_t)nc * sizeof(int));
                lr_nxt = (int *)xrealloc(lr_nxt, (size_t)nc * sizeof(int));
                nxt_cap = nc;
            }
            P[x].sd = tcd[i];
            mp2[w] = x;
            ar_nxt[x] = ar_head[w];
            ar_head[w] = x;
            if (!isH[c]) {
                lr_nxt[x] = lr_head[w];
                lr_head[w] = x;
            }
        }
        for (i = 0; i < tcn; i++) {
            int pw = tcp[i];
            if (pw < 0) continue;
            rt_link(mp2[tcb[i]], mp2[pw]);
        }
    }

    for (w = 0; w < N; w++) {
        int acnt = 0, lcnt = 0, x;
        for (x = ar_head[w]; x; x = ar_nxt[x]) apb[acnt++] = x;
        AP_[w] = 0;
        if (il[w]) {
            lfx[w] = acnt ? apb[0] : 0;
            acnt = 0;
        }
        if (acnt > 0) {
            int j;
            for (j = 0; j < acnt; j++) {
                bk[j] = P[apb[j]].c;
                bv[j] = apb[j];
            }
            AP_[w] = tbd(bk, bv, acnt);
        }
        for (x = lr_head[w]; x; x = lr_nxt[x]) ltb[lcnt++] = x;
        LR[w] = lt_bld(ltb, lcnt);
    }


    for (i = 0; i < nG; i++) {
        la_[i] = 0;
        dcc_[i] = 0;
        lm[i] = -1;
    }
    {
        int *lac = (int *)xcalloc((size_t)nG, sizeof(int));
        int *las = (int *)xmalloc((size_t)nG * sizeof(int));
        for (w = 0; w < N; w++) lac[gid[w]]++;
        las[0] = 0;
        for (i = 1; i < nG; i++) las[i] = las[i - 1] + lac[i - 1];
        memset(lac, 0, (size_t)nG * sizeof(int));
        for (w = 0; w < N; w++) {
            int g = gid[w];
            int idx = las[g] + lac[g]++;
            long long tv = LR[w] ? P[LR[w]].tmx : -1;
            bk[idx] = w;
            bv[idx] = tv;
            tt[pre[w]].tmx = tv;
        }
        for (i = 0; i < nG; i++) if (lac[i] > 0) la_[i] = abd(bk + las[i], bv + las[i], lac[i]);
        xfree(lac);
        xfree(las);
    }

    for (i = gqn - 1; i >= 0; i--) {
        int g = gq[i];
        int cnt = 0, e;
        for (e = dh_hd[g]; e != -1; e = dh_nx[e]) {
            int cg = dh_to[e];
            bk[cnt] = cg;
            bv[cnt] = lm[cg];
            cnt++;
        }
        dcc_[g] = (cnt > 0) ? abd(bk, bv, cnt) : 0;
        rlm(g);
    }
    for (i = 0; i < ndl; i++) lcol[i] = col[dlv[i]];
    {
        /* lidx[v] = number of leaves before v in pre-order, nlv[v] = leaves below v */
        int *lpre = (int *)xcalloc((size_t)(N + 1), sizeof(int));
        for (i = 0; i < ndl; i++) lpre[pre[dlv[i]] + 1] = 1;
        for (i = 1; i <= N; i++) lpre[i] += lpre[i - 1];
        for (i = 0; i < N; i++) {
            lidx[i] = lpre[pre[i]];
            nlv[i] = lpre[pre[i] + sz_[i]] - lpre[pre[i]];
        }
        xfree(lpre);
    }

    xfree(bk);
    xfree(bv);
    xfree(bc);
    xfree(bo);
    xfree(bt);
    xfree(ar_head);
    xfree(ar_nxt);
    xfree(lr_head);
    xfree(lr_nxt);
    xfree(ltb);
    xfree(apb);
    xfree(mp2);
}

static void stamp_next(void) {
    if (lstamp == INT_MAX) {
        memset(lst, 0, (size_t)nC * sizeof(int));
        lstamp = 1;
    } else {
        lstamp++;
    }
}

/* Walk the region of a non-DR node v in pre-order.  Returns the light maximum
   over the region's nodes and over the groups of its DR children.  The DR
   children are listed in drl (the first DSM_DR_CAP of them; ndrl counts all),
   and the colors of the region's leaves are counted in lcnt under stamp lstamp. */
static int drl[DSM_DR_CAP], ndrl;
static long long light_scan(int v) {
    int i = pre[v], e = i + sz_[v];
    long long b = -1;
    ndrl = 0;
    stamp_next();
    while (i < e) {
        const TT *t = &tt[i];
        if (t->grp >= 0) {
            long long l2 = lm[t->grp];
            if (l2 > b) b = l2;
            if (ndrl < DSM_DR_CAP) drl[ndrl] = t->grp;
            ndrl++;
            i += t->sz;
        } else {
            if (t->tmx > b) b = t->tmx;
            if (t->lc >= 0) {
                int c = t->lc;
                if (lst[c] != lstamp) {
                    lst[c] = lstamp;
                    lcnt[c] = 1;
                } else lcnt[c]++;
            }
            i++;
        }
    }
    return b;
}

static void query_impl(int v, int *rf, int *rc) {
    int i, L = nlv[v], bestf = 0, bestc = -1;
    if (L <= DSM_SCAN_BASE + DSM_SCAN_PER_HEAVY * nHv) {
        /* few leaves below v: count them directly (ties go to the smallest color) */
        int k = lidx[v], ke = k + L;
        stamp_next();
        for (; k < ke; k++) {
            int c = lcol[k], f;
            if (lst[c] != lstamp) {
                lst[c] = lstamp;
                lcnt[c] = 1;
                f = 1;
            } else f = ++lcnt[c];
            if (f > bestf || (f == bestf && c < bestc)) {
                bestf = f;
                bestc = c;
            }
        }
        *rf = bestf;
        *rc = bestc;
        return;
    }
    if (isDR[v]) {
        /* light part is maintained; heavy counts are in the group's row */
        long long b = lm[gid[v]];
        const int *row = hct + (size_t)gid[v] * hcap;
        if (b >= 0) {
            bestf = mf(b);
            bestc = mc2(b);
        }
        for (i = 0; i < nHv; i++) {
            int f = row[i], c = hvl[i];
            if (f > bestf || (f == bestf && f > 0 && c < bestc)) {
                bestf = f;
                bestc = c;
            }
        }
    } else {
        long long b = light_scan(v);
        if (b >= 0) {
            bestf = mf(b);
            bestc = mc2(b);
        }
        if (bestf < L) {
            if (ndrl <= DSM_DR_CAP) {
                /* region leaf counts plus the rows of the DR children */
                for (i = 0; i < nHv; i++) {
                    int c = hvl[i], f = (lst[c] == lstamp) ? lcnt[c] : 0, d;
                    for (d = 0; d < ndrl; d++) f += hct[(size_t)drl[d] * hcap + i];
                    if (f > bestf || (f == bestf && f > 0 && c < bestc)) {
                        bestf = f;
                        bestc = c;
                    }
                }
            } else {
                /* many DR children: rank queries on the per-color leaf trees */
                for (i = 0; i < nHv; i++) {
                    int c = hvl[i], fc;
                    if (freq[c] < bestf || (freq[c] == bestf && c > bestc)) continue;
                    fc = fvc(v, c);
                    if (fc > bestf || (fc == bestf && fc > 0 && c < bestc)) {
                        bestf = fc;
                        bestc = c;
                        if (bestf >= L) break;
                    }
                }
            }
        }
    }
    *rf = bestf;
    *rc = bestc;
}

static void hpush(int g) {
    int i = hn++;
    while (i > 0) {
        int p = (i - 1) >> 1;
        if (gpos[hq[p]] >= gpos[g]) break;
        hq[i] = hq[p];
        i = p;
    }
    hq[i] = g;
}

static int hpop(void) {
    int top = hq[0], g = hq[--hn], i = 0;
    while (1) {
        int l = 2 * i + 1, r = l + 1, m = i;
        int mg = g;
        if (l < hn && gpos[hq[l]] > gpos[mg]) { m = l; mg = hq[l]; }
        if (r < hn && gpos[hq[r]] > gpos[mg]) { m = r; mg = hq[r]; }
        if (m == i) break;
        hq[i] = hq[m];
        i = m;
    }
    if (hn > 0) hq[i] = g;
    return top;
}

static void update_impl(int v, int co, int cn) {
    int who, whn, nho, nhn, i;
    if (!il[v] || co == cn) return;
    who = isH[co];
    whn = isH[cn];
    if (afgen_ == INT_MAX) {
        memset(afv_, 0, (size_t)nG * sizeof(int));
        afgen_ = 1;
    } else {
        afgen_++;
    }
    naf_ = 0;

    tdel(&cL[co], tin[v]);
    freq[co]--;
    st_rem(v, co);
    if (who) hct_path_add(v, hidx[co], -1);

    nho = (freq[co] >= thr);
    if (who && !nho) {
        isH[co] = 0;
        hct_drop_column(hidx[co]);
        hidx[co] = -1;
        if (cL[co]) light_add_full(co);
    }

    nhn = ((freq[cn] + 1) >= thr);
    if (!whn && nhn) {
        if (cL[cn]) light_rem_full(cn);
        isH[cn] = 1;
        hidx[cn] = nHv;
        hvl[nHv++] = cn;
        hct_fill_column(cn, hidx[cn]);
    }

    col[v] = cn;
    lcol[lpos[v]] = cn;
    tt[pre[v]].lc = cn;
    freq[cn]++;
    tins(&cL[cn], tin[v], (long long)v);
    st_add(v, cn);
    if (isH[cn]) hct_path_add(v, hidx[cn], 1);

    /* propagate changed group maxima towards the root; a max-heap on the BFS
       position of the group processes every child group before its parent */
    hn = 0;
    for (i = 0; i < naf_; i++) hpush(afg_[i]);
    while (hn > 0) {
        int g = hpop();
        long long old = lm[g];
        rlm(g);
        if (lm[g] != old) {
            int pg = drp[g];
            if (pg >= 0) {
                achg(dcc_[pg], g, lm[g]);
                if (afv_[pg] != afgen_) {
                    afv_[pg] = afgen_;
                    hpush(pg);
                }
            }
        }
    }
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

void dsm_destroy(void) {
    free(_tp);
    free(_cb);
    free(_atp);
    free(dep);
    free(P);
    free(_lt_stk);
    free(LR);
    free(hd);
    free(nx);
    free(to);
    free(pa);
    free(tin);
    free(tout);
    free(tinv);
    free(il);
    free(col);
    free(dlv);
    free(es);
    free(ed);
    free(ef);
    free(_ds);
    free(_di);
    free(rbm);
    free(rbt);
    free(rsp);
    free(rlg);
    free(gid);
    free(groot);
    free(isDR);
    free(drp);
    free(dh_to);
    free(dh_nx);
    free(dh_hd);
    free(gq);
    free(_dw);
    free(_dq);
    free(tcb);
    free(tcf);
    free(tcp);
    free(tcd);
    free(_vs);
    free(_vc);
    free(_vidx);
    free(freq);
    free(isH);
    free(hvl);
    free(cL);
    free(cT);
    free(AP_);
    free(la_);
    free(dcc_);
    free(lm);
    free(afg_);
    free(afv_);
    free(pre);
    free(sz_);
    free(lidx);
    free(nlv);
    free(lpos);
    free(lcol);
    free(lst);
    free(lcnt);
    free(gpos);
    free(hq);
    free(tt);
    free(hct);
    free(hidx);
    free(lfx);
    lfx = NULL;
    hct = hidx = NULL;
    hcap = 0;
    pre = sz_ = lidx = nlv = lpos = lcol = lst = lcnt = gpos = hq = NULL;
    tt = NULL;
    lstamp = 0;
    hn = 0;
    api_ready = 0;
    MC = 0;
    _tp = NULL;
    _tp_cap = 0;
    _tp_cap_max = 0;
    _tn = 0;
    _fl = 0;
    _cb = NULL;
    _cc = 0;
    _atp = NULL;
    _atp_cap = 0;
    _atp_cap_max = 0;
    _atn = 0;
    _afl = 0;
    dep = NULL;
    P = NULL;
    _p_cap = 0;
    _p_cap_max = 0;
    pn_ = 0;
    pfr_ = 0;
    _lt_stk = NULL;
    LR = NULL;
    N = 0;
    Q = 0;
    nC = 0;
    alp = 0;
    hd = NULL;
    nx = NULL;
    to = NULL;
    ec = 0;
    pa = NULL;
    tin = NULL;
    tout = NULL;
    tmr_ = 0;
    tinv = NULL;
    il = NULL;
    col = NULL;
    dlv = NULL;
    ndl = 0;
    es = NULL;
    ed = NULL;
    ef = NULL;
    eln = 0;
    _ds = NULL;
    _di = NULL;
    rb = 0;
    rn = 0;
    rbm = NULL;
    rbt = NULL;
    rsp = NULL;
    rlg = NULL;
    rsp_levels = 0;
    memset(rlu, 0, sizeof(rlu));
    memset(rlo, 0, sizeof(rlo));
    B_sz = 0;
    thr = 0;
    gid = NULL;
    groot = NULL;
    nG = 0;
    isDR = NULL;
    drp = NULL;
    dh_to = NULL;
    dh_nx = NULL;
    dh_hd = NULL;
    dh_ec = 0;
    gq = NULL;
    gqn = 0;
    _dw = NULL;
    _dq = NULL;
    tcb = NULL;
    tcf = NULL;
    tcp = NULL;
    tcd = NULL;
    tcn = 0;
    _vs = NULL;
    _vc = NULL;
    _vidx = NULL;
    freq = NULL;
    isH = NULL;
    hvl = NULL;
    nHv = 0;
    cL = NULL;
    cT = NULL;
    AP_ = NULL;
    la_ = NULL;
    dcc_ = NULL;
    lm = NULL;
    afg_ = NULL;
    naf_ = 0;
    afv_ = NULL;
    afgen_ = 0;
}

int dsm_init(int n, int C, double alpha, const int *parents, const int *colors) {
    int i;
    if (n < 1 || C < 1 || !isfinite(alpha) || alpha < 0.0 || alpha > 1.0) return -1;
    if ((long long)n * 2 + 8 > INT_MAX) return -1;
    if (!valid_tree(n, C, parents, colors)) return -1;
    dsm_destroy();
    N = n;
    nC = C;
    alp = alpha;
    Q = 0;
    MC = (long long)nC;
    _tp_cap_max = capped_mul_add_int(N, 6, 8);
    _tp_cap = (_tp_cap_max < 16) ? _tp_cap_max : 16;
    _tp = (TN *)xmalloc((size_t)_tp_cap * sizeof(TN));
    _atp_cap_max = capped_mul_add_int(N, 2, 8);
    _atp_cap = (_atp_cap_max < 16) ? _atp_cap_max : 16;
    _atp = (AN *)xmalloc((size_t)_atp_cap * sizeof(AN));
    _p_cap_max = capped_mul_add_int(N, 5, 8);
    _p_cap = (_p_cap_max < 16) ? _p_cap_max : 16;
    P = xcalloc((size_t)_p_cap, sizeof(*P));
    _cb = (int *)xmalloc((size_t)N * sizeof(int));
    _lt_stk = (int *)xmalloc((size_t)N * sizeof(int));
    LR = (int *)xcalloc((size_t)N, sizeof(int));
    hd = (int *)xmalloc((size_t)N * sizeof(int));
    nx = (int *)xmalloc((size_t)2 * (size_t)N * sizeof(int));
    to = (int *)xmalloc((size_t)2 * (size_t)N * sizeof(int));
    pa = (int *)xmalloc((size_t)N * sizeof(int));
    dep = (int *)xmalloc((size_t)N * sizeof(int));
    tin = (int *)xmalloc((size_t)N * sizeof(int));
    tout = (int *)xmalloc((size_t)N * sizeof(int));
    tinv = (int *)xmalloc((size_t)2 * (size_t)N * sizeof(int));
    il = (int *)xmalloc((size_t)N * sizeof(int));
    col = (int *)xmalloc((size_t)N * sizeof(int));
    dlv = (int *)xmalloc((size_t)N * sizeof(int));
    es = (int *)xmalloc((size_t)2 * (size_t)N * sizeof(int));
    ed = (int *)xmalloc((size_t)2 * (size_t)N * sizeof(int));
    ef = (int *)xmalloc((size_t)N * sizeof(int));
    _ds = (int *)xmalloc((size_t)N * sizeof(int));
    _di = (int *)xmalloc((size_t)N * sizeof(int));
    gid = (int *)xmalloc((size_t)N * sizeof(int));
    groot = (int *)xmalloc((size_t)N * sizeof(int));
    isDR = (int *)xmalloc((size_t)N * sizeof(int));
    drp = (int *)xmalloc((size_t)N * sizeof(int));
    dh_to = (int *)xmalloc((size_t)N * sizeof(int));
    dh_nx = (int *)xmalloc((size_t)N * sizeof(int));
    dh_hd = (int *)xmalloc((size_t)N * sizeof(int));
    gq = (int *)xmalloc((size_t)N * sizeof(int));
    _dw = (int *)xmalloc((size_t)N * sizeof(int));
    _dq = (int *)xmalloc((size_t)N * sizeof(int));
    tcb = (int *)xmalloc((size_t)2 * (size_t)N * sizeof(int));
    tcf = (int *)xmalloc((size_t)2 * (size_t)N * sizeof(int));
    tcp = (int *)xmalloc((size_t)2 * (size_t)N * sizeof(int));
    tcd = (int *)xmalloc((size_t)2 * (size_t)N * sizeof(int));
    _vs = (int *)xmalloc((size_t)N * sizeof(int));
    _vc = (int *)xmalloc((size_t)N * sizeof(int));
    _vidx = (int *)xmalloc((size_t)N * sizeof(int));
    freq = (int *)xcalloc((size_t)nC, sizeof(int));
    isH = (int *)xcalloc((size_t)nC, sizeof(int));
    hvl = (int *)xmalloc((size_t)N * sizeof(int));
    cL = (int *)xcalloc((size_t)nC, sizeof(int));
    cT = (int *)xcalloc((size_t)nC, sizeof(int));
    AP_ = (int *)xcalloc((size_t)N, sizeof(int));
    la_ = (int *)xcalloc((size_t)N, sizeof(int));
    dcc_ = (int *)xcalloc((size_t)N, sizeof(int));
    lm = (long long *)xmalloc((size_t)N * sizeof(long long));
    afg_ = (int *)xmalloc((size_t)N * sizeof(int));
    afv_ = (int *)xcalloc((size_t)N, sizeof(int));
    pre = (int *)xmalloc((size_t)N * sizeof(int));
    sz_ = (int *)xmalloc((size_t)N * sizeof(int));
    lidx = (int *)xmalloc((size_t)N * sizeof(int));
    nlv = (int *)xmalloc((size_t)N * sizeof(int));
    lpos = (int *)xmalloc((size_t)N * sizeof(int));
    lcol = (int *)xmalloc((size_t)N * sizeof(int));
    lst = (int *)xcalloc((size_t)nC, sizeof(int));
    hidx = (int *)xmalloc((size_t)nC * sizeof(int));
    lcnt = (int *)xmalloc((size_t)nC * sizeof(int));
    gpos = (int *)xmalloc((size_t)N * sizeof(int));
    hq = (int *)xmalloc((size_t)N * sizeof(int));
    tt = (TT *)xmalloc((size_t)N * sizeof(TT));
    lfx = (int *)xcalloc((size_t)N, sizeof(int));
    lstamp = 0;
    hn = 0;

    memset(hd, -1, (size_t)N * sizeof(int));
    memset(tinv, -1, (size_t)2 * (size_t)N * sizeof(int));
    ec = 0;
    tmr_ = 0;
    eln = 0;
    ndl = 0;
    afgen_ = 0;
    pool_init();
    _tn = 1;
    _atn = 1;
    _fl = 0;
    _afl = 0;

    for (i = 1; i < N; i++) ae(parents[i], i);
    for (i = 0; i < N; i++) col[i] = colors[i];
    dfs();
    rmq_build();
    dsm_build();

    /* arrays used only during construction */
    free(dh_to); free(dh_nx); free(dh_hd); free(gq); free(dlv);
    dh_to = dh_nx = dh_hd = gq = dlv = NULL;

    api_ready = 1;
    return 0;
}

int dsm_update(int v, int color) {
    if (!api_ready || v < 0 || v >= N || color < 0 || color >= nC) return -1;
    if (!il[v]) return -1;
    update_impl(v, col[v], color);
    return 0;
}

int dsm_query(int v, int *color, int *frequency) {
    if (!api_ready || v < 0 || v >= N || !color || !frequency) return -1;
    query_impl(v, frequency, color);
    return 0;
}
