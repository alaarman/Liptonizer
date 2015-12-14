#include <assert.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>

#define PROBE_MAX 5

static int a1;
static int a2;
static int a3;
static int a4;
static int a5;
static int a6;
static int a7;
static int a8;

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
	for (int i = 0; i < PROBE_MAX; ++i) {
		*p1 = 1;
	}
	return NULL;
}
void *
w2 (void *x)
{
    for (int i = 0; i < PROBE_MAX; ++i) {
        *p2 = 2;
    }
    return NULL;
}
void *
w3 (void *x)
{
    for (int i = 0; i < PROBE_MAX; ++i) {
        *p3 = 3;
    }
    return NULL;
}
void *
w4 (void *x)
{
    for (int i = 0; i < PROBE_MAX; ++i) {
        *p4 = 4;
    }
    return NULL;
}
void *
w5 (void *x)
{
    for (int i = 0; i < PROBE_MAX; ++i) {
        *p5 = 5;
    }
    return NULL;
}
void *
w6 (void *x)
{
    for (int i = 0; i < PROBE_MAX; ++i) {
        *p6 = 6;
    }
    return NULL;
}
void *
w7 (void *x)
{
    for (int i = 0; i < PROBE_MAX; ++i) {
        *p7 = 7;
    }
    return NULL;
}
void *
w8 (void *x)
{
    for (int i = 0; i < PROBE_MAX; ++i) {
        *p8 = 8;
    }
    return NULL;
}

int
main ()
{
    if (__nondet_bool()) {
        p1 = &a1;
        p2 = &a2;
    } else {
        p2 = &a1;
        p1 = &a2;
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

	assert (a1 != a2);
//	assert (a2 != a3);
//	assert (a3 != a4);
//	assert (a4 != a5);
//	assert (a5 != a6);
//	assert (a6 != a7);
//	assert (a7 != a8);

	return 0;
}
