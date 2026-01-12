#include <stdio.h>
#include <stdlib.h>
int* buffer;
int head = 0;
int tail = 0;
int full = 0;
int const maxlen = 4;


/*@
  requires 0 <= head < maxlen;
  requires 0 <= tail < maxlen;
  requires full == 0 || full == 1;
  requires \valid(output_arr);
  requires \valid(buffer + (0 .. maxlen - 1));

  requires \separated(output_arr, buffer + (0 .. maxlen - 1), &head, &tail, &maxlen);

  assigns tail, *output_arr, full;

  behavior empty:
    assumes head == tail && !full;
    assigns \nothing;      
    ensures \result == -1;
    ensures tail == \old(tail);

  behavior success:
    assumes !(head == tail && !full);
    assigns tail, *output_arr, full;
    ensures \result == 0;
    
    ensures *output_arr == buffer[\old(tail)];
    ensures full == 0;

    ensures \old(tail) + 1 == maxlen ==> tail == 0;
    ensures \old(tail) + 1 != maxlen ==> tail == \old(tail) + 1;

  complete behaviors;
  disjoint behaviors;
*/
int get(int *output_arr) {
	int next;
	if (head == tail && !full)
		return -1; // buffer is empty

	next = tail + 1;
	if (next >= maxlen)
		next = 0;

	*output_arr = buffer[tail];
	
	tail = next;
	full = 0;
	// ghost int num_elements = (head - tail + maxlen) % maxlen;
	// assert num_elements >= 3 ==> (\forall integer i; 0 <= i <= num_elements - 3 ==> (buffer[(tail + i) % maxlen] + buffer[(tail + i + 1) % maxlen] == buffer[(tail + i + 2) % maxlen]));
	return 0;
}


/*@
  requires 0 <= head < maxlen;
  requires 0 <= tail < maxlen;
  requires full == 0 || full == 1;
  requires \valid(buffer + (0 .. maxlen - 1));
  
  requires \separated(buffer + (0 .. maxlen - 1), &head, &tail, &maxlen);

  assigns head, buffer[head], full;

  behavior full:
    assumes full;
    assigns \nothing;      
    ensures \result == -1;
    ensures head == \old(head);

  behavior success:
    assumes !full;
    assigns head, buffer[\old(head)], full;
    ensures \result == 0;
    ensures buffer[\old(head)] == data;
    
		ensures head == tail ==> full == 1;   
		ensures (head != tail) ==> full == 0;   
    ensures \old(head) + 1 == maxlen ==> head == 0;
    ensures \old(head) + 1 != maxlen ==> head == \old(head) + 1;

  complete behaviors;
  disjoint behaviors;
*/
int put(int data) {
	if (full)
		return -1;
	int next;
	next = head + 1;
	if (next >= maxlen)
		next = 0;
	
	buffer[head] = data;
	head = next;

	if (head == tail)
		full = 1;
	// ghost int num_elements = (head - tail + maxlen) % maxlen;
	// assert num_elements >= 3 ==> (\forall integer i; 0 <= i <= num_elements - 3 ==> (buffer[(tail + i) % maxlen] + buffer[(tail + i + 1) % maxlen] == buffer[(tail + i + 2) % maxlen]));
	return 0;
}

//@ ghost int count;
//@ assigns buffer, head, tail, count, full;
int main() {
	int data[4];
	buffer = data;
	int out[4];

	int a = 1;
	int b = 1;
	put(a);
    //@ ghost count = count + 1;
	put(b);
    //@ ghost count = count + 1;
    /*@ loop invariant 2 <= i <= maxlen-1;
        loop invariant 0 <= head <= maxlen - 1;
        loop invariant count == i;
        loop invariant full == 0 || full == 1;
        loop assigns i, buffer[0 .. maxlen - 1], head, a, b, count, full;
        loop variant maxlen - 1 - i; 
    */
	for (int i = 2; i < maxlen-1; i++) {
		int sum = a + b;
		 if(put(sum)) {
			  // Out of space
			 return -1;
		 }
        //@ ghost count = count + 1;
		a = b;
		b = sum;
	}

	// ghost int num_elements = (head - tail + maxlen) % maxlen;
	// assert num_elements >= 3 ==> (\forall integer i; 0 <= i <= num_elements - 3 ==> (buffer[(tail + i) % maxlen] + buffer[(tail + i + 1) % maxlen] == buffer[(tail + i + 2) % maxlen]));

    /*@ loop invariant 0 <= j <= maxlen-1;
        loop invariant 0 <= tail <= maxlen - 1;
        loop invariant count == maxlen - 1 - j;
        loop invariant full == 0 || full == 1;
        loop assigns j, out[0 .. maxlen - 1], tail, count, full;
        loop variant maxlen - 1 - j;
    */
	for (int j = 0; j < maxlen-1; j++) {
		if (get(&out[j])) {
			// Buffer is empty
			return -1;
		}
        //@ ghost count = count - 1;
	}
    //@ assert count == 0;
	return 0;
}
