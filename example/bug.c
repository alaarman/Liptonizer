/*
 */

#include <pthread.h>
#include <assert.h>
#include <stdlib.h>

int x = 1;

void *
thread( void *z )
{
    (void)z;
    x = 1;
    while (1) { };
    return NULL;
}

int
main()
{
    pthread_t tid;
    pthread_create( &tid, NULL, thread, NULL );
    assert( x == 0 );
    return x;
}
