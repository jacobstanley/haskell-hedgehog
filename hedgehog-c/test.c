#include "test.h"

#include <stdlib.h>

Array* new_array(int count)
{
    Array *x = (Array *)malloc(sizeof(Array));
    x->items = (int *)calloc(count, sizeof(int) * count);
    return x;
}
