#include <pthread.h>
#include <stdio.h>
#include <assert.h>
#include <unistd.h>

#define SIZE	  (10)
#define OVERFLOW  (-1)
#define UNDERFLOW (-2)

static int top=0;
unsigned int arr[SIZE];
int m=0; //pthread_mutex_t m;
_Bool flag=0; // FALSE

void *t1(void *arg) {
  for(int i=0; i<SIZE; i++) {
    __CPROVER_atomic_begin();__CPROVER_assume(m==0);m=1;__CPROVER_atomic_end();//pthread_mutex_lock(&m);
    assert(top!=SIZE);
    arr[top]=i;
    top++;
    printf("pushed element %d\n", i);
    flag=1;
    __CPROVER_atomic_begin();__CPROVER_assume(m==1);m=0;__CPROVER_atomic_end();//pthread_mutex_unlock(&m);
    usleep(1000); // helps trigger the bug
  }
}

void *t2(void *arg) {
  for(int i=0; i<SIZE; i++) {
    __CPROVER_atomic_begin();__CPROVER_assume(m==0);m=1;__CPROVER_atomic_end();//pthread_mutex_lock(&m);
    if (flag) {
      assert(top!=0);
      top--;
      printf("poped element: %d\n", arr[top]);
    }    
    __CPROVER_atomic_begin();__CPROVER_assume(m==1);m=0;__CPROVER_atomic_end();//pthread_mutex_unlock(&m);
  }
}

int main(void) {
  __CPROVER_ASYNC_1: t1(NULL);
  __CPROVER_ASYNC_1: t2(NULL);
  return 0;
}

// SIZE=5:  returns 'verification failed' after 1.8s
// SIZE=10: returns 'verification failed' after 1m2s
