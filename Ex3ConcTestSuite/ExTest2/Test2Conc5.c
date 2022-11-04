#include "../../Ex3.h"
#include "klee/klee.h"
#include <stdlib.h> 
#include <assert.h>

/*
  Property: If we create 3 nodes with different priorities, the node with the highest priority will be the first and the less will be the last
*/

int max (int arg1, int arg2, int arg3){
    if(arg1 > arg2 && arg1 > arg3){
        return arg1;
    } else if(arg2 > arg1 && arg2 > arg3){
        return arg2;
    } else if(arg3 > arg1 && arg3 > arg2){
        return arg3;
    }
    return -1;
}

int min (int arg1, int arg2, int arg3){
    if(arg1 < arg2 && arg1 < arg3){
        return arg1;
    } else if(arg2 < arg1 && arg2 < arg3){
        return arg2;
    } else if(arg3 < arg1 && arg3 < arg2){
        return arg3;
    }
    return -1;
}

int main() {
  int pri_a, pri_b, pri_c;
  int data_a, data_b, data_c;
  int maximum, minimum;

  
  pri_a = 536860670;
  pri_b = 553648128;
  pri_c = 536870913;
  data_a = 0;
  data_a = 0;
  data_a = 0;


  Queue queue = makeQueue();

  enqueue(queue, pri_a, data_a);
  enqueue(queue, pri_b, data_b);
  enqueue(queue, pri_c, data_c);


  maximum = max(pri_a,pri_b,pri_c);
  minimum = min(pri_a,pri_b,pri_c);

  assert(queue->fst->pri == maximum && queue->last->pri == minimum);

  return 0;
}