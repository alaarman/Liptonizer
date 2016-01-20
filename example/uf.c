#include <assert.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>

static const int EMPTY = 0;
static const int FULL = -1;

static const int PROBE_MAX = 5;

#define N 10

static int tree[N] = { 0, 0, 0, 0, 0, 0, 0, 0, 0 };

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
process (void *arg)
{
  //pthread_join(ht_init,0);
  int val = *(int *)arg;
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

    pthread_t t[T];
	for (int i = 0; i < T; i++)
		pthread_create (t + i, NULL, process, (void *) &value[i]);

	int found_total = 0;
	//long res;
	for (int i = 0; i < T; i++) {
		pthread_join (t[i], NULL);// (void **)&res);
		found_total += 1;//res;
	}
	//assert (found_total == 4); // T - (unique values in value array)
	return 0;
}
