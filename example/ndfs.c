extern unsigned int __VERIFIER_nondet_uint();
//pthread/stack_true-unreach-call.c:    tmp = __VERIFIER_nondet_uint()%SIZE;

#include <assert.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>


#define T       10
#define MAX     10

typedef struct node_s node_t;

typedef enum color_e {
    white,
    blue,
    cyan
} color_t;

struct node_s {
    bool            accepting;

    color_t         color[T];
    bool            red;
    bool            pink[T];
    size_t          count;
};

node_t               s0;

struct successors_s {
    node_t          N[MAX];
    size_t          count;
};

typedef struct successors_s successors_t;

void
init_node (node_t *s)
{
    s->accepting = __VERIFIER_nondet_uint() % 2;
    s->red = __VERIFIER_nondet_uint() % 2;
    s->count = __VERIFIER_nondet_uint() % T;
    for (int i = 0; i < T; i++) {
        s->pink[i] = __VERIFIER_nondet_uint() % 2;
        s->color[i] = __VERIFIER_nondet_uint() % 3;
    }
}

static inline void
init_successors (successors_t *next)
{
    next->count = __VERIFIER_nondet_uint() % MAX;
    next->N[next->count ];
    for (int i = 0; i < next->count; i++) {
        init_node (&next->N[i]);
    }
}

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

static inline bool
all_pink_or_red_not_cyan (successors_t *next, int p)
{
    for (size_t i = 0; i < next->count; i++)
        if (!pink_or_red_not_cyan(&next->N[i], p)) return false;
    return true;
}

static inline bool
all_blue_cyan_or_red (successors_t *next, int p)
{
    for (size_t i = 0; i < next->count; i++)
        if (!blue_cyan_or_red(&next->N[i], p)) return false;
    return true;
}

void
dfsred (node_t *s, int p)
{
    node_t *t;
    successors_t next;
    init_successors (&next);

    assert (all_blue_cyan_or_red(&next, p));
    s->pink[p] = true;
    int i = 0;

    for (int i = 0; i < next.count; i++) {
        t = &next.N[i];
        if (t->color[p] == cyan) exit(1);
        if (!s->pink[p] && !t->red) {
            dfsred(t, p);
        }
    }

    if (s->accepting) {
        __sync_fetch_and_add (&s->count, -1); // count -= 1
        while (*((volatile size_t *)&s->count) > 0) {}
    }

    assert (all_pink_or_red_not_cyan(&next, p));
    s->red = true;
    s->pink[p] = false;
}

void
dfsblue (node_t *s, int p)
{
    node_t *t;
    successors_t next;
    init_successors (&next);

    s->color[p] = cyan;
    int i = 0;
    for (int i = 0; i < next.count; i++) {
        t = &next.N[i];
        if (t->color[p] == white && !t->red) {
            dfsblue (t, p);
        }
    }
    if (s->accepting) {
        __sync_fetch_and_add (&s->count, 1); // count += 1
        dfsred (s, p);
    }

    assert (all_blue_cyan_or_red(&next, p));
    s->color[p] = blue;
}

void *
ndfs (void *x)
{
    int t = (size_t) x;
    dfsblue (&s0, t);
    return NULL;
}

int
main ()
{
    init_node (&s0);

    pthread_t threads[T];
    for (size_t i = 0; i < T; i++) {
        pthread_create (&threads[i], NULL, ndfs, (void *)i);
    }
    for (int i = 0; i < T; i++) {
        pthread_join (threads[i], NULL);
    }
    return 0;
}
