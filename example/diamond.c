#include <vvt.h>
#include <assert.h>
#include <pthread.h>

int active_thread = 0;
int value = 0;
pthread_mutex_t lock;

void* worker(void* arg) {
  int thid = (int)arg;
  while(thid!=active_thread) {
  }
  pthread_mutex_lock(&lock);
  value += thid;
  pthread_mutex_unlock(&lock);
  return 0;
}

void* selector(void* arg) {
  while(true) {
    active_thread = __nondet_int();
  }
}

int main() {
  pthread_t sel;
  pthread_create(&sel,0,selector,0);
  pthread_t t1,t2,t3;
  pthread_create(&t1,0,worker,1);
  pthread_create(&t2,0,worker,2);
  pthread_create(&t3,0,worker,3);
  pthread_join(t1,0);
  pthread_join(t2,0);
  pthread_join(t3,0);
  assert(value==6);
  return 0;
}
