
typedef struct Array_s
{
    int *items;
} Array;

Array* new_array(int size);

int add(Array *xs, int n);
