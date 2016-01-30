#include <assert.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>

#define LENGTH 10

static int a1[LENGTH];
static int a2[LENGTH];
static int a3[LENGTH];
static int a4[LENGTH];
static int a5[LENGTH];
static int a6[LENGTH];
static int a7[LENGTH];
static int a8[LENGTH];

static int *p1;
static int *p2;
static int *p3;
static int *p4;
static int *p5;
static int *p6;
static int *p7;
static int *p8;

void *
w1 (void *x)
{
    for (int i = 0; i < LENGTH - 1; ++i) {
        assume (p1[i] < p1[i + 1]);
    }
    return NULL;
}
void *
w2 (void *x)
{
    for (int i = 0; i < LENGTH - 1; ++i) {
        assume (p2[i] < p2[i + 1]);
    }
    return NULL;
}
void *
w3 (void *x)
{
    for (int i = 0; i < LENGTH - 1; ++i) {
        assume (p3[i] < p3[i + 1]);
    }
    return NULL;
}
void *
w4 (void *x)
{
    for (int i = 0; i < LENGTH - 1; ++i) {
        assume (p4[i] < p4[i + 1]);
    }
    return NULL;
}
void *
w5 (void *x)
{
    for (int i = 0; i < LENGTH - 1; ++i) {
        assume (p5[i] < p5[i + 1]);
    }
    return NULL;
}
void *
w6 (void *x)
{
    for (int i = 0; i < LENGTH - 1; ++i) {
        assume (p6[i] < p6[i + 1]);
    }
    return NULL;
}
void *
w7 (void *x)
{
    for (int i = 0; i < LENGTH - 1; ++i) {
        assume (p7[i] < p7[i + 1]);
    }
    return NULL;
}
void *
w8 (void *x)
{
    for (int i = 0; i < LENGTH - 1; ++i) {
        assume (p8[i] < p8[i + 1]);
    }
    return NULL;
}

int
main ()
{
    if (__nondet_bool()) {
        p1 = a1;
        p2 = a2;
    } else {
        p2 = a1;
        p1 = a2;
    }

    pthread_t t1;
    pthread_t t2;
    pthread_t t3;
    pthread_t t4;
    pthread_t t5;
    pthread_t t6;
    pthread_t t7;
    pthread_t t8;
    //for (int i = 0; i < T; i++)
        pthread_create (&t1, NULL, w1, NULL);//(void *) &value[i]);
        pthread_create (&t2, NULL, w2, NULL);//(void *) &value[i]);
        //pthread_create (&t3, NULL, w3, NULL);//(void *) &value[i]);
        //pthread_create (&t4, NULL, w4, NULL);//(void *) &value[i]);
        //pthread_create (&t5, NULL, w5, NULL);//(void *) &value[i]);
        //pthread_create (&t6, NULL, w6, NULL);//(void *) &value[i]);
        //pthread_create (&t7, NULL, w7, NULL);//(void *) &value[i]);
        //pthread_create (&t8, NULL, w8, NULL);//(void *) &value[i]);

        pthread_join (t1, NULL);// (void **)&res);
        pthread_join (t2, NULL);// (void **)&res);
//        pthread_join (t3, NULL);// (void **)&res);
//        pthread_join (t4, NULL);// (void **)&res);
//        pthread_join (t5, NULL);// (void **)&res);
//        pthread_join (t6, NULL);// (void **)&res);
//        pthread_join (t7, NULL);// (void **)&res);
//        pthread_join (t8, NULL);// (void **)&res);

//    int out[LENGTH * T];
//    // merge:
//    for (int i  = 0; i < LENGTH; i++) {
//        out[i + i] = a1[i];
//        out[i + i + 1] = a2[i];
//    }

    assert (a1[0] <= a1[1]);
    assert (a2[0] <= a2[1]);
//  assert (a2 != a3);
//  assert (a3 != a4);
//  assert (a4 != a5);
//  assert (a5 != a6);
//  assert (a6 != a7);
//  assert (a7 != a8);

    return 0;
}
