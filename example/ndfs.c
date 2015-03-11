//pthread/stack_true-unreach-call.c:    tmp = __VERIFIER_nondet_uint()%SIZE;

#include <assert.h>
#include <limits.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define NO 0
#define VERIFIER 1
#define TEST 2

#define RANDOM_GRAPH NO


#define DODEBUG

#define T           10
#define MAX         10
#define STACK_MAX   10


#ifdef DODEBUG
#define print printf
#else
#define print(x,y,z) 0
#endif

typedef enum color_e {
    white,
    blue,
    cyan
} color_t;


typedef struct node_s node_t;
struct node_s {
    int             id;
    bool            acc;

    color_t        *color;
    bool           *pink;
    bool            red;
    size_t          count;

    int             num;
    int            *succs;
};



static node_t             *s0;

typedef struct stack_elem_s stack_elem_t;
struct stack_elem_s {
    node_t         *s;
    size_t          index;
    stack_elem_t   *prev;
    node_t        **next;
};

static inline bool
pink_or_red_not_cyan (node_t *t, int p)
{
    return (t->red || t->pink[p]) && t->color[p] != cyan;
}

static inline bool
blue_cyan_or_red (node_t *t, int p)
{
    return t->color[p] == blue || t->color[p] == cyan || t->red;
}


extern unsigned int randuint();

#if RANDOM_GRAPH==VERIFIER

extern unsigned int __VERIFIER_nondet_uint();

inline unsigned int
randuint ()
{
    return __VERIFIER_nondet_uint();
}
#endif

#if RANDOM_GRAPH==TEST


typedef unsigned long long u64b;
typedef unsigned __int128 u128b;

u64b rng_hash_128(u64b *s)
{
    u64b c = 7319936632422683419ULL;
    u64b x = s[1];
    u64b y = s[0];
    u128b xx;

    /* Increment 128bit LCG */
    s[0] += c;
    s[1] += (s[0] < c) + y;

    /* Default threaded option of xoring seed location */
    x ^= (u64b) s;

    /* Hash result */
    xx = (u128b)x * c;
    x = xx ^ y ^ (xx >> 64);
    xx = (u128b)x * c;
    return xx + y + (xx >> 64);
}

static __thread u64b seed[2];

inline unsigned int
randuint ()
{
    return rng_hash_128 (seed);
}
#endif


#if RANDOM_GRAPH

/**
 * Generate nodes according to preserved invariants
 */

static inline void
rand_red (node_t *s)
{
    s->red = randuint() % 2;
}

static inline void
rand_color (node_t *s, int p)
{
    s->color[p] = randuint() % 3;
}

static inline void
rand_local (node_t *prev, node_t *s, int p)
{
    rand_color (s, p);
    s->pink[p] = randuint() % 2;

    while (prev && prev->pink[p] && !blue_cyan_or_red(s, p)) {
        rand_red (s);
        rand_color (s, p);
    }
}

static inline void
rand_node (node_t *prev, node_t *s)
{
    rand_red (s);
    s->id = randuint() % 100;
    s->acc = randuint() % 2;
    s->count = 0;//randuint() % (T -1); //TODO
    s->num = randuint() % MAX;
    for (int i = 0; i < T; i++) {
        rand_local (prev, s, i);
    }
}

node_t *
init_node (node_t *prev, int index)
{
    node_t *s = malloc (sizeof (node_t));
    s->color = malloc (sizeof (color_t[T]));
    s->pink = malloc (sizeof (bool[T]));
    rand_node (prev, s);
    return s;
    (void) prev;
}

void
deinit_node (node_t *s)
{
    free (s->color);
    free (s->pink);
    free (s);
}

#else

#define WHITE   (color_t[T]){white}
#define FALSE   (bool[T]){false}
#define INIT    .color=WHITE, .pink=FALSE, .red=false, .count=0

static node_t graph[] = {
    { .id=0, .acc=false, INIT, .succs=(int[]){0, 1, 2}, .num=3 },
    { .id=1, .acc=true , INIT, .succs=(int[]){2}, .num=1 },
    { .id=2, .acc=true , INIT, .succs=(int[]){3}, .num=1 },
    { .id=3, .acc=false, INIT, .succs=(int[]){3}, .num=1 },
};

node_t *
init_node (node_t *prev, int index)
{
    if (prev == NULL)
        return &graph[ 0 ];
    return &graph[ prev->succs[index] ];
}

void deinit_node (node_t *s) {}

#endif

static inline void
delete_successors (stack_elem_t *stack)
{
    for (int i = 0; i < stack->s->num; i++) {
        deinit_node (stack->next[i]);
    }
    free (stack->next);
    free (stack);
}

static inline stack_elem_t *
create_successors (stack_elem_t *prev, node_t *s)
{
    stack_elem_t *elem = malloc (sizeof (stack_elem_t));
    elem->next = malloc (sizeof (node_t *[s->num]));
    elem->index = 0;
    elem->s = s;
    elem->prev = prev;
    for (int i = 0; i < s->num; i++) {
        elem->next[i] = init_node (s, i);
    }
    return elem;
}

static inline bool
all_pink_or_red_not_cyan (stack_elem_t *n, int p)
{
    for (size_t i = 0; i < n->s->num; i++)
        if (!pink_or_red_not_cyan(n->next[i], p)) {
            return false;
        }
    return true;
}

static inline bool
all_blue_cyan_or_red (stack_elem_t *n, int p)
{
    for (size_t i = 0; i < n->s->num; i++)
        if (!blue_cyan_or_red(n->next[i], p)) {
            return false;
        }
    return true;
}

static stack_elem_t *
stack_pop (stack_elem_t *stack)
{
    stack_elem_t *prev = stack->prev;
    delete_successors (stack);
    return prev;
}

void
dfsred (int p, stack_elem_t *stack)
{
    stack_elem_t *seed = stack;
    assert (all_blue_cyan_or_red(stack, p));
print ("[%d] pink %d\n", p, stack->s->id);
    stack->s->pink[p] = true;
    while (stack) {
        node_t *s = stack->s;
        if (stack->index != s->num) {
            node_t *t = stack->next[stack->index++]; // popSuccessor
            if (t->color[p] == cyan) {
                print ("[%d] FOUND %d\n", p, t->id);
                exit(1);
            }
            if (!t->pink[p] && !t->red) {
                assert (all_blue_cyan_or_red(stack, p));
                t->pink[p] = true;
print ("[%d] pink %d\n", p, t->id);
                stack = create_successors (stack, t);
            }
        } else { // backtrack:
            if (s->acc) {
                __sync_fetch_and_add (&s->count, -1); // count -= 1
                while (*((volatile size_t *)&s->count) > 0) {}
            }
            assert (all_pink_or_red_not_cyan(stack, p));
print ("[%d] red %d\n", p, s->id);
            s->red = true;
            s->pink[p] = false;

            if (stack == seed) return; // dfsblue does cleanup
            stack = stack_pop (stack);
        }
    }
}

void
dfsblue (int p, stack_elem_t *stack)
{
print ("[%d] cyan %d\n", p, stack->s->id);
    stack->s->color[p] = cyan;
    while (stack) {
        node_t *s = stack->s;
        if (stack->index != s->num) {
            node_t *t = stack->next[stack->index++]; // popSuccessor
            if (t->color[p] == white && !t->red) {
                t->color[p] = cyan;
print ("[%d] cyan %d\n", p, t->id);
                stack = create_successors (stack, t);
            }
        } else { // backtrack:
            assert (all_blue_cyan_or_red(stack, p));
            if (s->acc) {
                __sync_fetch_and_add (&s->count, 1); // count += 1
                stack->index = 0; // rewind
                dfsred (p, stack);
            }
print ("[%d] blue %d\n", p, s->id);
            s->color[p] = blue;
            stack = stack_pop (stack);
        }
    }
}

void *
ndfs (void *x)
{
    int p = (size_t) x;
#if RANDOM_GRAPH == TEST
    seed[0] = (p+1) * 7319936632422683419ULL;
    seed[1] = (p+2) * 7319936632422683419ULL;
#endif

    stack_elem_t *stack = create_successors (NULL, s0);
    dfsblue (p, stack);
    return NULL;
}

int
main ()
{
    s0 = init_node (NULL, 0);

    pthread_t threads[T];
    for (size_t i = 0; i < T; i++) {
        pthread_create (&threads[i], NULL, ndfs, (void *)i);
    }
    for (size_t i = 0; i < T; i++) {
        pthread_join (threads[i], NULL);
    }

    deinit_node (s0);
    return 0;
}
