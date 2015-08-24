
#include <pthread.h>
#include <stdlib.h>
#include <assert.h>

//#define BUG

#ifndef NUM_OF_READERS
#define NUM_OF_READERS     2
#endif

#ifndef NUM_OF_WRITERS
#define NUM_OF_WRITERS     2
#endif

// stream of exchanged data = INITIAL, INITIAL + 1, ... , EOF - 1, EOF
#ifndef INITIAL
#define INITIAL            1
#endif
#ifndef EOF
#define EOF                5
#endif

int global = INITIAL;
int writers = 0;
int readers = 0;
pthread_mutex_t mutex; // mutex for readers
pthread_rwlock_t rwlock;

static inline void check() {
    // ( writers != 0 ) => ( writers = 1 and readers = 0 )
    assert( !writers || ( writers == 1 && !readers ) );
}

void global_write() {
    __sync_fetch_and_add(&writers, 1);

    check();
    ++global;

    __sync_fetch_and_add(&writers, -1);
}

int global_read() {
    __sync_fetch_and_add(&readers, 1);

    check();
    int local = global;

    __sync_fetch_and_add(&readers, -1);

    return local;
}

void *reader( void *arg ) {
    (void) arg;

    // read initial value
    pthread_rwlock_rdlock( &rwlock );
    int local = global_read();
    //assert( local == INITIAL );
    pthread_rwlock_unlock( &rwlock );

    while ( local != EOF ) {

#ifndef BUG
        pthread_rwlock_rdlock( &rwlock );
#endif

        local = global_read();
        // Here the thread would continue with reading and processing of loaded data
        // (which won't change meanwhile, if the read lock is obtained).
        assert( local == global_read() ); // fails with macro BUG defined

#ifndef BUG
        pthread_rwlock_unlock( &rwlock );
#endif
    }

    return NULL;
}

void *writer( void *arg ) {
    (void) arg;
    int local;

    do {
        pthread_rwlock_wrlock( &rwlock );
        local = global_read();
        if ( local != EOF ) {
            // here the thread would produce next value
            global_write();
        }
        pthread_rwlock_unlock( &rwlock );
    } while ( local != EOF );

    return NULL;
}

int main() {
    int i;
    pthread_t readers[NUM_OF_READERS];
    pthread_t writers[NUM_OF_WRITERS];

    pthread_mutex_init( &mutex, NULL );
    pthread_rwlock_init( &rwlock, NULL );

    // create threads
    for ( i = 0; i < NUM_OF_READERS; i++ )
        pthread_create( &readers[i], NULL, reader, NULL );

    for ( i = 0; i < NUM_OF_WRITERS; i++ )
        pthread_create( &writers[i], NULL, writer, NULL );

    // join threads
    for ( i = 0; i < NUM_OF_READERS; i++ )
        pthread_join( readers[i], NULL );

    for ( i = 0; i < NUM_OF_WRITERS; i++ )
        pthread_join( writers[i], NULL );

    assert( global == EOF );
    pthread_mutex_destroy( &mutex );
    pthread_rwlock_destroy( &rwlock );
    return 0;
}
