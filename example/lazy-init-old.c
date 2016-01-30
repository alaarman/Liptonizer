#include <assert.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>

#define PROBE_MAX 4 // should be even!

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

int T[20] = {-1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20};


void *
process (void *x)
{
    if (T[0] == -1) { // lazy initialization
        /**
         * Simulate swapping in array with CAS using one write, because for
         * lack of interpolation techniques we do not currently support
         * dynamically allocated arrays.
         */

        //for (int i = 0; i < PROBE_MAX; ++i) {
            int i = 0;
            T[i] = i + 1;
        //}
    }

    int total = 0;
    for (int i = 0; i < PROBE_MAX; i++) {
        total += T[i];
    }

    assert (total == (PROBE_MAX / 2 * (PROBE_MAX + 1)));
    return NULL;
}

int
main ()
{
    pthread_t t1;
    pthread_t t2;
    pthread_t t3;
    pthread_t t4;
    pthread_t t5;
    pthread_t t6;
    pthread_t t7;
    pthread_t t8;
    //for (int i = 0; i < T; i++)
        pthread_create (&t1, NULL, process, NULL);//(void *) &value[i]);
        pthread_create (&t2, NULL, process, NULL);//(void *) &value[i]);
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

    return 0;
}
