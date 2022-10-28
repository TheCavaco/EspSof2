#include <assert.h>
#include <klee/klee.h>
#include "../../Ex3.h"





int main(){
    int pri_a, pri_b, pri_c;
    int data_a, data_b, data_c;

    
    pri_a = 0;
    pri_b = 2147483647;
    pri_c = 0;
    data_a = 0;
    data_a = 0;
    data_a = 0;


    Queue queue = makeQueue();

    enqueue(queue, pri_a, data_a);
    enqueue(queue, pri_b, data_b);
    enqueue(queue, pri_c, data_c);

    assert(queue->count == 3);



    return 0;
}