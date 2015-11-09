/*
 *	File  : pbzip2.cpp
 *	Author: Jeff Gilchrist (http://gilchrist.ca/jeff/)
 *	Date  : April 17, 2010
 */
#include "mini-pbzip2-safe.h"
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

static int NumBlocks = 0;
static int NextBlockToWrite;
static size_t OutBufferPosToWrite;
static outBuff *OutputBuffer;
int OutputBuffer_length; // instrumented variable
static queue *fifo;
static pthread_mutex_t OutMutex;
static pthread_cond_t *notTooMuchNumBuffered;

void outputBufferAdd(outBuff *element);
void queue_add(queue *this_queue, ElementTypePtr element);
int queue_remove(queue *this_queue, ElementTypePtr *element);

void *fileWriter(void *__)
{
  int currBlock = 0;
  size_t outBufferPos = 0;
  while (true)
    {
      if (currBlock >= MAX)
	{
	  // We're done
	  break;
	}
      pthread_mutex_lock(&OutMutex);
      // 1st array bound check
      assert(outBufferPos<OutputBuffer_length);
      if ((OutputBuffer[outBufferPos].buf == INVALID))
	{
	  pthread_mutex_unlock(&OutMutex);
	  //	  usleep(50000); // without usleep, pccw is faster
	  continue;
	}
      else
	{
	  pthread_mutex_unlock(&OutMutex);
	}
      // 2nd array bound check
      assert(outBufferPos<OutputBuffer_length);
      outBuff * outBlock = &(OutputBuffer[outBufferPos]);
      printf("FW: I read block number %d.\n", outBlock->blockNumber);
      outBlock->buf = INVALID;
      if (++outBufferPos == NumBufferedBlocksMax)
	{
	  outBufferPos = 0;
	}
      ++currBlock;
      pthread_mutex_lock(&OutMutex);
      ++NextBlockToWrite;
      OutBufferPosToWrite = outBufferPos;
      pthread_cond_broadcast(notTooMuchNumBuffered);
      pthread_mutex_unlock(&OutMutex);
    } // while
  return (NULL);
}

int producer()
{
  char *FileData;
  NumBlocks = 0;
  while (1)
    {
      FileData = (char *)VALID;
      pthread_mutex_lock(fifo->mut);
      while (fifo->full)
	{
	  pthread_cond_wait(fifo->notFull, fifo->mut);
	}
      outBuff *queueElement = (outBuff *) malloc(sizeof(outBuff));
      queueElement->buf = FileData; queueElement->blockNumber = NumBlocks;
      printf("PR: I produced block number %d.\n", queueElement->blockNumber);
      queue_add(fifo, queueElement);
      pthread_cond_signal(fifo->notEmpty);
      ++NumBlocks;
      pthread_mutex_unlock(fifo->mut);
      if (NumBlocks == MAX) { break; }
    } // while
  pthread_cond_broadcast(fifo->notEmpty); // just in case
  return 0;
}

void *consumer(void *__)
{
  outBuff *fileData;
  for (;;)
    {
      //assert (fifo->mut != NULL);
      pthread_mutex_lock(fifo->mut);
      for (;;)
	{
	  if (!fifo->empty && (queue_remove(fifo, &fileData) == 1))
	    {
	      break;
	    }
	  pthread_cond_wait(fifo->notEmpty, fifo->mut);
	}
      //      printf("CO: I read block number %d.\n", fileData->blockNumber);
      pthread_cond_signal(fifo->notFull);
      pthread_mutex_unlock(fifo->mut);
      outBuff outBlock;
      outBlock.buf = fileData->buf; outBlock.blockNumber = fileData->blockNumber;
      outputBufferAdd(&outBlock);
      //      printf("CO: I wrote block number %d.\n", outBlock.blockNumber);
      free(fileData);
    } // for
}

queue *queueInit(int queueSize)
{
  queue *q;
  q = (queue *) malloc(sizeof(queue));
  q->qData = (outBuff **) malloc(sizeof(outBuff *)*queueSize);
  q->size = queueSize;
  q->empty = 1;
  q->full = 0;
  q->head = 0;
  q->tail = 0;
  q->mut = (pthread_mutex_t *) malloc(sizeof(pthread_mutex_t));
  pthread_mutex_init(q->mut, NULL);
  q->notFull = (pthread_cond_t *) malloc(sizeof(pthread_cond_t));
  pthread_cond_init(q->notFull, NULL);
  q->notEmpty = (pthread_cond_t *) malloc(sizeof(pthread_cond_t));
  pthread_cond_init(q->notEmpty, NULL);
  notTooMuchNumBuffered = (pthread_cond_t *) malloc(sizeof(pthread_cond_t));
  pthread_cond_init(notTooMuchNumBuffered, NULL);
  return (q);
}

void queueDelete (queue *q)
{
  pthread_mutex_destroy(q->mut);
  free(q->mut);
  pthread_cond_destroy(q->notFull);
  free(q->notFull);
  pthread_cond_destroy(q->notEmpty);
  free(q->notEmpty);
  free(q->qData);
  free(q);
  pthread_cond_destroy(notTooMuchNumBuffered);
  free(notTooMuchNumBuffered);
  return;
}

void queue_add(queue *this_queue, ElementTypePtr element)
{
  (this_queue->qData)[this_queue->tail] = element;
  ++(this_queue->tail);
  
  if (this_queue->tail == this_queue->size)
    this_queue->tail = 0;
  if (this_queue->tail == this_queue->head)
    this_queue->full = 1;
  
  this_queue->empty = 0;
}

int queue_remove(queue *this_queue, ElementTypePtr *element)
{
  ElementTypePtr *headElem = &(this_queue->qData)[this_queue->head];
 
  *element = *headElem;
  ++(this_queue->head);
  
  if (this_queue->head == this_queue->size)
    this_queue->head = 0;
  if (this_queue->head == this_queue->tail)
    this_queue->empty = 1;
  
  this_queue->full = 0;
  
  return 1;
}

void outputBufferInit(size_t size)
{
  int i;
  pthread_mutex_lock(&OutMutex);
  NextBlockToWrite = 0;
  OutBufferPosToWrite = 0;
  OutputBuffer_length = size;
  OutputBuffer = (outBuff *) malloc(sizeof(outBuff)*size);
  for (i=0; i<size; i++) {
    // 3nd array bound check
    assert(0 <= i && i<size);
    OutputBuffer[i].buf = INVALID;
  }
  pthread_mutex_unlock(&OutMutex);
}

void outputBufferAdd(outBuff *element)
{
  pthread_mutex_lock(&OutMutex);
  int dist = element->blockNumber - NumBufferedBlocksMax;
  while (dist >= NextBlockToWrite)
    {
      pthread_cond_wait(notTooMuchNumBuffered, &OutMutex);
    }
  size_t outBuffPos = OutBufferPosToWrite + element->blockNumber - NextBlockToWrite;
  if (outBuffPos >= NumBufferedBlocksMax)
    {
      outBuffPos -= NumBufferedBlocksMax;
    }
  // 4th array bound check
  // assert(0<=outBuffPos && outBuffPos<OutputBuffer_length);
  //OutputBuffer[outBuffPos] = *element;
  OutputBuffer[outBuffPos].buf = element->buf;
  OutputBuffer[outBuffPos].bufSize = element->bufSize;
  OutputBuffer[outBuffPos].blockNumber = element->blockNumber;
  OutputBuffer[outBuffPos].inSize = element->inSize;
  pthread_mutex_unlock(&OutMutex);
  return;
}

int main(int argc, char* argv[])
{
  pthread_t consumer_t1;
  pthread_t consumer_t2;
  pthread_t fileWriter_t;
  //OutMutex = (pthread_mutex_t *) malloc(sizeof(pthread_mutex_t));
  pthread_mutex_init(&OutMutex, NULL);
  fifo = queueInit(2);
  outputBufferInit(NumBufferedBlocksMax);
  pthread_create(&consumer_t1, NULL, consumer, NULL);
  pthread_create(&consumer_t2, NULL, consumer, NULL);
  pthread_create(&fileWriter_t, NULL, fileWriter, NULL);
  producer();
  pthread_join(fileWriter_t, NULL);
  pthread_kill(consumer_t1, SIGKILL);
  pthread_kill(consumer_t2, SIGKILL);
  free(OutputBuffer);
  queueDelete(fifo);
  pthread_mutex_destroy(&OutMutex);
  //free(OutMutex);
  return 0;
}

