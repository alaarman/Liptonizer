#include <stdio.h>
#include <pthread.h>

int mx=0, my=0;
int x=2, y=2;

void *thread1() {
	int a;
	__CPROVER_atomic_begin();__CPROVER_assume(mx==0);mx=1;__CPROVER_atomic_end();
	a = x;
	__CPROVER_atomic_begin();__CPROVER_assume(my==0);my=1;__CPROVER_atomic_end();
	y = y + a;
	y = y + a;
	y = y + a;
	y = y + a;
	y = y + a;
	y = y + a;
	y = y + a;
	y = y + a;
	y = y + a;
	y = y + a;
	my = 0;
	a = a + 1;		
	__CPROVER_atomic_begin();__CPROVER_assume(my==0);my=1;__CPROVER_atomic_end();
	y = y + a;
	y = y + a;
	y = y + a;
	y = y + a;
	y = y + a;
	y = y + a;
	y = y + a;
	y = y + a;
	y = y + a;
	y = y + a;
	my = 0;
	x = x + x + a;
	mx=0;
	assert(x!=47);
}

void *thread2() {
	__CPROVER_atomic_begin();__CPROVER_assume(mx==0);mx=1;__CPROVER_atomic_end();
	x=x+2;
	x=x+2;
	x=x+2;
	x=x+2;
	x=x+2;
	x=x+2;
	x=x+2;
	x=x+2;
	x=x+2;
	x=x+2;
	mx=0;
}

void *thread3() {
	__CPROVER_atomic_begin();__CPROVER_assume(my==0);my=1;__CPROVER_atomic_end();
	y=y+2;
	y=y+2;
	y=y+2;
	y=y+2;
	y=y+2;
	y=y+2;
	y=y+2;
	y=y+2;
	y=y+2;
	y=y+2;
	my=0;
	y=2;
}

int main() {
  __CPROVER_ASYNC_1: thread1();
  __CPROVER_ASYNC_1: thread2();
  __CPROVER_ASYNC_1: thread3();
  return 0;
}

// Impara 'stopped' after ??minutes
