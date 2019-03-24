#include <stdlib.h>
#include <stdio.h>

#include "circularbuffer.h"

struct CircularBuffer {
    int* data;
    int in_p;
    int out_p;
    int size;
};

CircularBuffer* circbuffer_create(int size) {
    CircularBuffer* ret = malloc(sizeof(CircularBuffer));
    ret->data = malloc(sizeof(int) * (size + 1));
    ret->size = size + 1;
    ret->in_p = 0;
    ret->out_p = 0;
    return ret;
}

void circbuffer_destroy(CircularBuffer* q) {
    if(q) {
        free(q->data);
        free(q);
    }
}

void circbuffer_put(CircularBuffer* q, int i) {
    q->data[q->in_p] = i;
    q->in_p = (q->in_p + 1) % q->size;
}

int circbuffer_get(CircularBuffer* q) {
    int ret = q->data[q->out_p];
    q->out_p = (q->out_p + 1) % q->size;
    return ret;
}

int circbuffer_size(CircularBuffer* q) {
    // printf("Val in = %d\nout = %d\nsize = %d\n =%d\n\n", q->in_p, q->out_p, q->size, (q->in_p - q->out_p + q->size) % q->size);
    return (q->in_p - q->out_p + q->size) % q->size;
}
