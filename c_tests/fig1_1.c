#include <stdio.h>
#include <pthread.h>

pthread_mutex_t mx, my;
int x=2, y=2;

void *thread1() {
	int a;
	pthread_mutex_lock(&mx);
	a = x;
	pthread_mutex_lock(&my);
	y = y + a;
	pthread_mutex_unlock(&my);
	a = a + 1;		
	pthread_mutex_lock(&my);
	y = y + a;
	pthread_mutex_unlock(&my);
	x = x + x + a;
	pthread_mutex_unlock(&mx);
	assert(x!=11);
}

void *thread2() {
	pthread_mutex_lock(&mx);
	x=x+2;
	pthread_mutex_unlock(&mx);
}

void *thread3() {
	pthread_mutex_lock(&my);
	y=y+2;
	pthread_mutex_unlock(&my);
}

int main() {
  pthread_t t1, t2, t3;
  pthread_mutex_init(&mx, 0);
  pthread_mutex_init(&my, 0);
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
  pthread_create(&t3, 0, thread3, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  pthread_join(t3, 0);
  pthread_mutex_destroy(&mx);
  pthread_mutex_destroy(&my);
  return 0;
}

// Threader-OG '-no-main' returns 'program is correct' in 6.3s
