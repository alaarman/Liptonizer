#include <assert.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>

static const int EMPTY = 0;
static const int FULL = -1;

static const int PROBE_MAX = 5;

#define N 10

//hash(x) := x / 10
//static int table[N] = { 1, 9, 7, 0, 41, 55, 58, 52, 0, 0 };

//hash(x) := x % 10
static int table[N] = { 59, 1, 50, 20, 0, 55, 65, 7, 0, 9 };


//int table[N] = { 0, 0, 0, 0, 0, 0, 0, 0, 0 };

int
find_or_insert (int val)
{
	int h = val % N;

	int index = h;
	for (int i = 0; i < PROBE_MAX; ++i) {
#ifdef DEBUG
	    printf ("checking for %d loc %d value found %d\n", val, index, table[index]);
#endif
		if (table[index] == EMPTY) {
			int success = __sync_bool_compare_and_swap(&table[index], EMPTY, val);
			if (success) {
				return 0;
			}
		}
		if (table[index] == val) {
			return 1;
		}

		index++;
		index = index < N ? index : 0; // mod N
	}
	return FULL;
}

void *
process1 (void *arg)
{
  //pthread_join(ht_init,0);
  int val = 30;//(int )arg;
  int found = find_or_insert (val);
  assert (!found);// != FULL);
#ifdef DEBUG
  printf ("%d = %s\n", val, found ? "found" : "inserted");
#endif
  return NULL;//(void *) (long) found; // pthread_exit( (void *) found )
}

void *
process2 (void *arg)
{
  //pthread_join(ht_init,0);
  int val = 59;//(int )arg;
  int found = find_or_insert (val);
  assert (found);// != FULL);
#ifdef DEBUG
  printf ("%d = %s\n", val, found ? "found" : "inserted");
#endif
  return NULL;//(void *) (long) found; // pthread_exit( (void *) found )
}

void *
process3 (void *arg)
{
  //pthread_join(ht_init,0);
  int val = 65;//(int )arg;
  int found = find_or_insert (val);
  assert (found);// != FULL);
#ifdef DEBUG
  printf ("%d = %s\n", val, found ? "found" : "inserted");
#endif
  return NULL;//(void *) (long) found; // pthread_exit( (void *) found )
}

void *
process4 (void *arg)
{
  //pthread_join(ht_init,0);
  int val = 20;//(int )arg;
  int found = find_or_insert (val);
  assert (found);// != FULL);
#ifdef DEBUG
  printf ("%d = %s\n", val, found ? "found" : "inserted");
#endif
  return NULL;//(void *) (long) found; // pthread_exit( (void *) found )
}

void *
process5 (void *arg)
{
  //pthread_join(ht_init,0);
  int val = 50;//(int )arg;
  int found = find_or_insert (val);
  assert (found);// != FULL);
#ifdef DEBUG
  printf ("%d = %s\n", val, found ? "found" : "inserted");
#endif
  return NULL;//(void *) (long) found; // pthread_exit( (void *) found )
}

void *
process6 (void *arg)
{
  //pthread_join(ht_init,0);
  int val = 55;//(int )arg;
  int found = find_or_insert (val);
  assert (found);// != FULL);
#ifdef DEBUG
  printf ("%d = %s\n", val, found ? "found" : "inserted");
#endif
  return NULL;//(void *) (long) found; // pthread_exit( (void *) found )
}


void *
process7 (void *arg)
{
  //pthread_join(ht_init,0);
  int val = 41;//(int )arg;
  int found = find_or_insert (val);
  assert (found);// != FULL);
#ifdef DEBUG
  printf ("%d = %s\n", val, found ? "found" : "inserted");
#endif
  return NULL;//(void *) (long) found; // pthread_exit( (void *) found )
}


void *
process8 (void *arg)
{
  //pthread_join(ht_init,0);
  int val = 52;//(int )arg;
  int found = find_or_insert (val);
  assert (found);// != FULL);
#ifdef DEBUG
  printf ("%d = %s\n", val, found ? "found" : "inserted");
#endif
  return NULL;//(void *) (long) found; // pthread_exit( (void *) found )
}


#define T 2				// threads
int value[T] = {  1, 59, };//9, };// 52, 41  };
int
main ()
{
//    // fill table
//    find_or_insert (1);
//    find_or_insert (52);
//    find_or_insert (41);
//    find_or_insert (55);
//    find_or_insert (7);
//    find_or_insert (9);
//    find_or_insert (59);
    int v1 = 1;
    int v2 = 59;

    pthread_t t1;
    pthread_t t2;
    pthread_t t3;
    pthread_t t4;
    pthread_t t5;
    pthread_t t6;
    pthread_t t7;
    pthread_t t8;
	//for (int i = 0; i < T; i++)
		pthread_create (&t1, NULL, process1, NULL);//(void *) &value[i]);
		pthread_create (&t2, NULL, process2, NULL);//(void *) &value[i]);
        pthread_create (&t3, NULL, process3, NULL);//(void *) &value[i]);
        pthread_create (&t4, NULL, process4, NULL);//(void *) &value[i]);
        //pthread_create (&t5, NULL, process5, NULL);//(void *) &value[i]);
        //pthread_create (&t6, NULL, process6, NULL);//(void *) &value[i]);
        //pthread_create (&t7, NULL, process7, NULL);//(void *) &value[i]);
        //pthread_create (&t8, NULL, process8, NULL);//(void *) &value[i]);

	int found_total = 0;
	//long res;
//	for (int i = 0; i < T; i++) {
		pthread_join (t1, NULL);// (void **)&res);
		found_total += 1;//res;
		pthread_join (t2, NULL);// (void **)&res);
		found_total += 1;//res;
        pthread_join (t3, NULL);// (void **)&res);
        found_total += 1;//res;
        pthread_join (t4, NULL);// (void **)&res);
        found_total += 1;//res;
        //pthread_join (t5, NULL);// (void **)&res);
        //found_total += 1;//res;
        //pthread_join (t7, NULL);// (void **)&res);
        //found_total += 1;//res;
        //pthread_join (t8, NULL);// (void **)&res);
        //found_total += 1;//res;
//	}
	//assert (found_total == 4); // T - (unique values in value array)
	return 0;
}
