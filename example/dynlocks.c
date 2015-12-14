#include <assert.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>

#define PROBE_MAX 10

static int last = -1;
static int shared = 0;

static pthread_mutex_t a1;
static pthread_mutex_t a2;
static pthread_mutex_t a3;
static pthread_mutex_t a4;
static pthread_mutex_t a5;
static pthread_mutex_t a6;
static pthread_mutex_t a7;
static pthread_mutex_t a8;

static pthread_mutex_t *p1;
static pthread_mutex_t *p2;
static pthread_mutex_t *p3;
static pthread_mutex_t *p4;
static pthread_mutex_t *p5;
static pthread_mutex_t *p6;
static pthread_mutex_t *p7;
static pthread_mutex_t *p8;

void *
w1 (void *x)
{
    pthread_mutex_lock (p1);
	for (int i = 0; i < PROBE_MAX; ++i) {
		last = 1;
		shared = 1;
	}
	pthread_mutex_unlock (p1);
	return NULL;
}
void *
w2 (void *x)
{
    pthread_mutex_lock (p2);
    for (int i = 0; i < PROBE_MAX; ++i) {
        last = 2;
        shared = 2;
    }
    pthread_mutex_unlock (p2);
    return NULL;
}

int
main ()
{
    if (__nondet_bool()) {
        p1 = &a1;
        p2 = &a1;
        pthread_mutex_init (&a1, NULL);
    } else {
        p1 = &a2;
        p2 = &a2;
        pthread_mutex_init (&a2, NULL);
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

	assert (last == shared);
//	assert (a2 == a3);
//	assert (a3 == a4);
//	assert (a4 == a5);
//	assert (a5 == a6);
//	assert (a6 == a7);
//	assert (a7 == a8);

	return 0;
}
