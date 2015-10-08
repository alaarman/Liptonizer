#include <vvt.h>
#include <assert.h>
#include <pthread.h>
#include <stdbool.h>

#define N 3

int table[N];
bool initialized = false;
int min=1024;
int max=0;

void* initializer(void* arg) {
  int i;
  for(i=0;i<N;++i) {
    int j = __nondet_int();
    assume(j>0 && j<1024);
    table[i] = j;
  }
  initialized = true;
  return NULL;
}

void* calc_min(void* arg) {
  while(!initialized) {}
  int i;
  int _min=1024;
  for(i=0;i<N;++i) {
    int tmp = table[i];
    if(tmp<_min) {
      _min = tmp;
    }
  }
  min = _min;
  return NULL;
}

void* calc_max(void* arg) {
  while(!initialized) {}
  int i;
  int _max = 0;
  for(i=0;i<N;++i) {
    int tmp = table[i];
    if(tmp>_max) {
      _max = tmp;
    }
  }
  max = _max;
  return NULL;
}

int main() {
  pthread_t t_init,t_min,t_max;
  pthread_create(&t_init,0,initializer,0);
  pthread_create(&t_min,0,calc_min,0);
  pthread_create(&t_max,0,calc_max,0);
  pthread_join(t_init,0);
  pthread_join(t_min,0);
  pthread_join(t_max,0);
  assert(min<=max);
  return 0;
}
