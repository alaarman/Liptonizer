#include <pthread.h>
#include <stdio.h>
#include <assert.h>
#include <unistd.h>

#define SIZE	  (5)
#define OVERFLOW  (-1)
#define UNDERFLOW (-2)

static int top=0;
unsigned int arr[SIZE];
pthread_mutex_t m;
_Bool flag=0; // FALSE

void *t1(void *arg) {
  for(int i=0; i<SIZE; i++) {
    pthread_mutex_lock(&m);
    assert(top!=SIZE);
    arr[top]=i;
    top++;
    printf("pushed element %d\n", i);
    flag=1;
    pthread_mutex_unlock(&m);
    usleep(1000); // helps trigger the bug
  }
}

void *t2(void *arg) {
  for(int i=0; i<SIZE; i++) {
    pthread_mutex_lock(&m);
    if (flag) {
      assert(top!=0);
      top--;
      printf("poped element: %d\n", arr[top]);
    }    
    pthread_mutex_unlock(&m);
  }
}

int main(void) {
  pthread_t id1, id2;
  pthread_mutex_init(&m, 0);
  pthread_create(&id1, NULL, t1, NULL);
  pthread_create(&id2, NULL, t2, NULL);
  pthread_join(id1, NULL);
  pthread_join(id2, NULL);
  return 0;
}

/* ./cream --debug --no-main --algorithm:owicki-gries
 SIZE=5:  returns 'feasible' after 1.6s
 SIZE=10: returns 'feasible' after 2.3s
 SIZE=20: 'stopped' after ??minutes
*/

/* ./cream --debug --no-main --algorithm:rely-guarantee
 SIZE=5:  'stopped' after ??minutes
 SIZE=10: 'stopped' after ??minutes
*/
