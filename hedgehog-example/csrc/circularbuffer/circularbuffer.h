#ifndef _CIRCULAR_BUFFER_H_
#define _CIRCULAR_BUFFER_H_
typedef struct CircularBuffer CircularBuffer;

CircularBuffer* circbuffer_create(int size);

void circbuffer_destroy(CircularBuffer* r);

void circbuffer_put(CircularBuffer* r, int i);
int circbuffer_get(CircularBuffer* r);
int circbuffer_size(CircularBuffer* r);

#endif
