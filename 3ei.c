/*
    Board lay-out:
     0   1   2       9  12  15      18  19  20
     3   4   5      10  13  16      21  22  23
     6   7   8      11  14  17      24  25  26
    Bottom layer    Middle layer    Top layer

    board.x     bitmask of fields occupied by player 1
    board.o     bitmask of fields occupied by player 2
    board.h[n]  number of pieces stacked on or above field n
    board.m     number of moves played
*/

#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>
#include <time.h>
#include <assert.h>

#define FOR(i,a,b) for(i = (a); i != (b); ++i)
#define REP(i,n)   FOR(i, 0, n)

#define BIT(n)     (1<<n)
#define FLD(i,j,k) (3*(i) + (j) + 9*(k))
#define OCC(i,j,k) (BIT(FLD(i,j,k)))

typedef struct board
{
    int x, o, h[9], m;
} board_t;

typedef struct cache_entry
{
    struct cache_entry *next;
    int x, o, value;
} cache_entry_t;

static int winlines[27][16];  /* need at least 13+1 */
static board_t board;

#define MAXCACHE 10000007
static cache_entry_t *cache[MAXCACHE];
static cache_entry_t cache_entries[MAXCACHE];
static size_t cache_size = 0;

static void print_board(FILE *fp, const board_t *board)
{
    int i, j, k;
    fprintf(fp, "board after %d move%s (heights: ",
                board->m, board->m == 1 ? "" : "s");
    REP(i, 9) {
        if (i > 0 && i%3 == 0) fputc(' ', fp);
        fputc(board->h[i] + '0', fp);
    }
    fprintf(fp, ")\n");
    REP(i, 3) {
        REP(k, 3) {
            if (k > 0) fputs("  ", fp);
            REP(j, 3) {
                if (j > 0) fputc(' ', fp);
                fputc( (board->x&OCC(i,j,k)) ? 'x' :
                       (board->o&OCC(i,j,k)) ? 'o' : '.', fp );
            }
        }
        fputc('\n', fp);
    }
}

static int solve(int x, int o, int h[9], int m)
{
    int n, value;
    cache_entry_t *ce = NULL;

    /* lookup cached result */
    {
        cache_entry_t **p;
        p = &cache[((46351u*x) ^ o)%MAXCACHE];
        while (*p != NULL && (*p)->x != x && (*p)->o != o) p = &(*p)->next;
        if (*p != NULL) return (*p)->value;
        assert(cache_size < MAXCACHE);
        ce = *p = &cache_entries[cache_size++];
        ce->next = NULL;
        ce->x = x;
        ce->o = o;
    }
    if (m == 27) return 0;

    /* check for winning moves */
    REP(n, 9) if (h[n] < 3) {
        int f = n + 9*h[n], nx = x|BIT(f), *w;
        for (w = &winlines[f][0]; *w != 0; ++w) {
            if ((nx&*w) == *w) {
                value = +27;
                goto solved;
            }
        }
    }

    /* solve recursively */
    value = -99;
    REP(n, 9) if (h[n] < 3) {
        int f = n + 9*(h[n]++);
        int v = -solve(o, x|BIT(f), h, m + 1);
        h[n]--;
        if (v > value) value = v;
    }
    assert(value != -99);
    if (value < 0) ++value;
    if (value > 0) --value;

solved:
    if (ce != NULL) ce->value = value;
    return value;
}

static int solve_board(board_t *board)
{
    return solve(board->m&1 ? board->o : board->x,
                 board->m&1 ? board->x : board->o,
                 board->h, board->m);
}

static int cmp_int(const void *a, const void *b)
{
    return *(int*)a - *(int*)b;
}

static int *remove_duplicates(int *begin, int *end)
{
    int *new_end;
    if (begin == end) return end;
    qsort(begin, end - begin, sizeof(*begin), &cmp_int);
    for (new_end = ++begin; begin != end; ++begin)
        if (*begin != begin[-1])
            *new_end++ = *begin;
    return new_end;
}

static void init_winlines()
{
    int i, j, k, di, dj, dk, n, lines[26], *end;
    REP(i, 3) REP(j, 3) REP(k, 3) {
        end = lines;
        FOR(di, -1, 2) FOR(dj, -1, 2) FOR(dk, -1, 2) if (di || dj || dk) {
            int line = OCC(i, j, k), bits = 1;
            FOR(n, -2, 3) if (n) {
                int ni = i + n*di, nj = j + n*dj, nk = k + n*dk;
                if (ni >= 0 && ni < 3 && nj >= 0 && nj < 3 && nk >= 0 && nk < 3)
                {
                    line |= OCC(ni, nj, nk);
                    ++bits;
                }
            }
            if (bits == 3) *end++ = line;
        }
        assert(end - lines <= sizeof(lines)/sizeof(*lines));
        end = remove_duplicates(lines, end);
        assert(end - lines <  sizeof(*winlines)/sizeof(**winlines));
        for (n = 0; &lines[n] != end; ++n)
            winlines[FLD(i, j, k)][n] = lines[n];
    }
}

static bool is_valid_move(const board_t *board, int i, int j)
{
    return i >= 0 && i < 3 && j >= 0 && j < 3 && board->h[3*i + j] < 3;
}

static void do_move(board_t *board, int i, int j)
{
    int *x, k;
    assert(is_valid_move(board, i, j));
    x = (board->m++)&1 ? &board->o : &board->x;
    k = board->h[3*i + j]++;
    assert((*x&OCC(i, j, k)) == 0);
    *x |= OCC(i, j, k);
}

static void undo_move(board_t *board, int i, int j)
{
    int *x, k;
    x = (--board->m)&1 ? &board->o : &board->x;
    assert(board->h[3*i + j] > 0);
    k = --board->h[3*i + j];
    assert((*x&OCC(i, j, k)) != 0);
    *x &= ~OCC(i, j, k);
}

static bool is_winning_move(const board_t *board, int i, int j)
{
    int f, nx, *w;
    assert(is_valid_move(board, i, j));
    f = FLD(i, j, board->h[3*i + j]);
    nx = ((board->m)&1 ? board->o : board->x)|BIT(f);
    for (w = &winlines[f][0]; *w != 0; ++w) {
        if ((nx&*w) == *w) return true;
    }
    return false;
}

static bool pick_move(board_t *board, int *i_out, int *j_out)
{
    int i, j, v, best_i[9], best_j[9], n = 0, best_v = -99;
    REP(i, 3) REP(j, 3) if (is_valid_move(board, i, j)) {
        if (is_winning_move(board, i, j)) {
            v = +27;
        } else {
            do_move(board, i, j);
            v = -solve_board(board);
            undo_move(board, i, j);
        }
        if (v > best_v) best_v = v, n = 0;
        if (v >= best_v) {
            best_i[n] = i;
            best_j[n] = j;
            ++n;
        }
    }
    if (n == 0) return false;
    if (best_v > 0) printf("AI: win in %d moves :-)\n", 1 + (27 - best_v)/2);
    if (best_v < 0) printf("AI: loss in %d moves :-(\n", 1 + (best_v + 27)/2);
    if (best_v == 0) printf("AI: draw :-/\n");
    n = rand()%n;
    *i_out = best_i[n];
    *j_out = best_j[n];
    return true;
}

static void cache_check()
{
    int cnt[11] = { }, n;
    REP(n, MAXCACHE) {
        cache_entry_t *bucket = cache[n];
        int c = 0;
        while (bucket && c <= 10) { ++c; bucket = bucket->next; }
        ++cnt[c];
    }
    printf("Cache capacity:   %8d\n", (int)MAXCACHE);
    printf("Cache population: %8d\n", (int)cache_size);
    printf("Bucket size frequencies:\n");
    REP(n, 9) printf("  %d  entries: %8d\n", n, cnt[n]);
    printf(" 10+ entries: %8d\n", cnt[10]);
}

int main(int argc, char *argv[])
{
    int ai, i, j, over;
    srand(time(NULL));
    if (argc != 2) {
        printf("usage: 3ei <ai>\n");
        exit(1);
    }
    ai = atoi(argv[1]) - 1;
    init_winlines();
    over = 0;
    print_board(stdout, &board);
    while (!over)
    {
        if (ai >= 0 && board.m >= ai && (board.m&1) == (ai&1)) {
            if (!pick_move(&board, &i, &j)) {
                printf("no move found!\n");
                break;
            }
            printf("AI plays %d %d\n", i, j);
        } else {
            char line[64];
        read_move:
            fputs("> ", stdout);
            fflush(stdout);
            if (!fgets(line, sizeof(line), stdin)) {
                printf("end of input!\n");
                break;
            }
            if (sscanf(line, "%d %d", &i, &j) != 2) {
                printf("invalid input!\n");
                goto read_move;
            }
            if (!is_valid_move(&board, i, j)) {
                printf("invalid move!\n");
                goto read_move;
            }
        }
        if (is_winning_move(&board, i, j)) over = 1;
        do_move(&board, i, j);
        print_board(stdout, &board);
        if (over) printf("player %d has won!\n", 2 - (board.m&1));
        if (board.m == 27) over = 1;
    }
    return 0;
}
