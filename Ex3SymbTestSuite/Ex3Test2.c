#include "../Ex3.h"
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

  
  klee_make_symbolic(&pri_a, sizeof(int), "pri_a");
  klee_make_symbolic(&pri_b, sizeof(int), "pri_b");
  klee_make_symbolic(&pri_c, sizeof(int), "pri_c");


  klee_make_symbolic(&data_a, sizeof(int), "data_a");
  klee_make_symbolic(&data_b, sizeof(int), "data_b");
  klee_make_symbolic(&data_c, sizeof(int), "data_c");


  klee_assume(pri_a >= 0);
  klee_assume(pri_b >= 0);
  klee_assume(pri_c >= 0);

  klee_assume(pri_a != pri_b);
  klee_assume(pri_b != pri_c);
  klee_assume(pri_c != pri_a);



  Queue queue = makeQueue();

  enqueue(queue, pri_a, data_a);
  enqueue(queue, pri_b, data_b);
  enqueue(queue, pri_c, data_c);


  maximum = max(pri_a,pri_b,pri_c);
  minimum = min(pri_a,pri_b,pri_c);

  assert(queue->fst->pri == maximum && queue->last->pri == minimum);

  return 0;
}