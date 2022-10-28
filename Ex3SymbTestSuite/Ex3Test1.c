#include "../Ex3.h"
#include "klee/klee.h"
#include <stdlib.h> 
#include <assert.h>

/*
  Property: Queueing valid elements preserves the validity of the Queue
*/



int main() {
  int pri_a, pri_b, pri_c;
  int data_a, data_b, data_c;
  klee_make_symbolic(&pri_a, sizeof(int), "pri_a");
  klee_make_symbolic(&pri_b, sizeof(int), "pri_b");
  klee_make_symbolic(&pri_c, sizeof(int), "pri_c");


  klee_make_symbolic(&data_a, sizeof(int), "data_a");
  klee_make_symbolic(&data_b, sizeof(int), "data_b");
  klee_make_symbolic(&data_c, sizeof(int), "data_c");


  klee_assume(pri_a >= 0);
  klee_assume(pri_b >= 0);
  klee_assume(pri_c >= 0);


  Queue queue = makeQueue();

  enqueue(queue, pri_a, data_a);
  enqueue(queue, pri_b, data_b);
  enqueue(queue, pri_c, data_c);

  assert(validQueue(queue));

  return 0;
}