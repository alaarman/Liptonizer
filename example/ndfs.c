extern unsigned int __VERIFIER_nondet_uint();
//pthread/stack_true-unreach-call.c:    tmp = __VERIFIER_nondet_uint()%SIZE;

#include <assert.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>


#define T           10
#define MAX         10
#define STACK_MAX   10


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



#define WHITE   (color_t[T]){white}
#define FALSE   (bool[T]){false}
#define INIT    .color=WHITE, .pink=FALSE, .red=false, .count=0

static node_t graph[] = {
    { .id=0, .acc=false, INIT, .succs=(int[]){0, 1, 2}, .num=3 },
    { .id=1, .acc=true , INIT, .succs=(int[]){2}, .num=1 },
    { .id=2, .acc=true , INIT, .succs=(int[]){3}, .num=1 },
    { .id=3, .acc=false, INIT, .succs=(int[]){3}, .num=1 },
};

static node_t state0;
static node_t             *s0 = &state0; // &graph[0];


typedef struct stack_elem_s stack_elem_t;
struct stack_elem_s {
    node_t         *s;
    size_t          index;
    stack_elem_t   *prev;
    node_t         *next;
};

void
init_node (node_t *s, node_t *prev, int index)
{
    s->acc = __VERIFIER_nondet_uint() % 2;
    s->red = __VERIFIER_nondet_uint() % 2;
    s->count = __VERIFIER_nondet_uint() % T; // TODO: T - 1?
    s->num = __VERIFIER_nondet_uint() % MAX;
    for (int i = 0; i < T; i++) {
        s->pink[i] = __VERIFIER_nondet_uint() % 2;
        s->color[i] = __VERIFIER_nondet_uint() % 3;
    }
    (void) prev;
}

static inline void
delete_successors (stack_elem_t *stack)
{
    free (stack->next);
    free (stack);
}

static inline stack_elem_t *
create_successors (stack_elem_t *prev, node_t *s)
{
    stack_elem_t *elem = malloc (sizeof (stack_elem_t));
    elem->next = malloc (sizeof (node_t[s->num]));
    elem->index = 0;
    elem->s = s;
    elem->prev = prev;
    for (int i = 0; i < s->num; i++) {
        init_node (&elem->next[i], s, i);
    }
    return elem;
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
all_pink_or_red_not_cyan (stack_elem_t *n, int p)
{
    for (size_t i = 0; i < n->s->num; i++)
        if (!pink_or_red_not_cyan(&n->next[i], p)) return false;
    return true;
}

static inline bool
all_blue_cyan_or_red (stack_elem_t *n, int p)
{
    for (size_t i = 0; i < n->s->num; i++)
        if (!blue_cyan_or_red(&n->next[i], p)) return false;
    return true;
}

void
dfsred (int p, stack_elem_t *stack)
{
    stack_elem_t *seed = stack;
    //assert (all_blue_cyan_or_red(stack, p)); // TODO: pink_p \subseteq blue \cup cyan_p
    stack->s->pink[p] = true;
    while (stack) {
        node_t *s = stack->s;
        if (stack->index != s->num) {
            node_t *t = &stack->next[stack->index++]; // popSuccessor
            if (t->color[p] == cyan) exit(1);
            if (!t->pink[p] && !t->red) {
                //assert (all_blue_cyan_or_red(stack, p)); // TODO: pink_p \subseteq blue \cup cyan_p
                t->pink[p] = true;
                stack = create_successors (stack, t);
            }
        } else { // backtrack:
            if (s->acc) {
                __sync_fetch_and_add (&s->count, -1); // count -= 1
                while (*((volatile size_t *)&s->count) > 0) {}
            }
            assert (all_pink_or_red_not_cyan(stack, p));
            s->red = true;
            s->pink[p] = false;

            if (stack == seed) return; // dfsblue does cleanup
            stack_elem_t *stackp = stack;
            stack = stack->prev;
            delete_successors(stackp);
        }
    }
}

void
dfsblue (int p, stack_elem_t *stack)
{
    stack->s->color[p] = cyan;
    while (stack) {
        node_t *s = stack->s;
        if (stack->index != s->num) {
            node_t *t = &stack->next[stack->index++]; // popSuccessor
            if (t->color[p] == white && !t->red) {
                t->color[p] = cyan;
                stack = create_successors (stack, t);
            }
        } else { // backtrack:
            assert (all_blue_cyan_or_red(stack, p));
            if (s->acc) {
                __sync_fetch_and_add (&s->count, 1); // count += 1
                dfsred (p, stack);
            }
            s->color[p] = blue;
            stack_elem_t *stackp = stack;
            stack = stack->prev;
            delete_successors(stackp);
        }
    }
}

void *
ndfs (void *x)
{
    int t = (size_t) x;

    stack_elem_t *stack = create_successors (stack, s0);
    dfsblue (t, stack);
    return NULL;
}

int
main ()
{
    init_node (s0, NULL, 0);

    pthread_t threads[T];
    for (size_t i = 0; i < T; i++) {
        pthread_create (&threads[i], NULL, ndfs, (void *)i);
    }
    for (size_t i = 0; i < T; i++) {
        pthread_join (threads[i], NULL);
    }
    return 0;
}
