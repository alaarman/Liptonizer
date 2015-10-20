/* 
 * File:   pbzip2.h
 * Author: Yavor Nikolov
 *
 * Created on March 6, 2010, 10:18 PM
 */
#include <pthread.h> 
#include <utime.h>
#include <inttypes.h>
#include <stdbool.h>

#define	FILE_MODE	(S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH)
#define OFF_T		off_t
#define O_BINARY 0
#define numCPU 2
// #define NumBufferedBlocksMax (100000000 / (9*100000))
#define NumBufferedBlocksMax 4
#define MAX 5000
#define INVALID NULL
#define VALID 1

typedef struct outBuff
{
  char *buf;
  unsigned int bufSize;
  int blockNumber;
  unsigned int inSize;
} outBuff;

#define DSIZE 2

typedef outBuff ElementType;
typedef ElementType* ElementTypePtr;
typedef struct queue
{
	ElementTypePtr qData[DSIZE];
	long size;
	long head, tail;
	int full, empty;
	pthread_mutex_t mut;
	//pthread_cond_t *notFull, *notEmpty;
} queue;
