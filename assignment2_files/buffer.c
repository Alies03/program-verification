int* buffer;
int head = 0;
int tail = 0;
int const maxlen = 4;


/*@
  requires 0 <= head < maxlen;
  requires 0 <= tail < maxlen;
  requires \valid(output_arr);
  requires \valid(buffer + (0 .. maxlen - 1));

  // Crucial: Ensure the output pointer doesn't point to our internal variables
  requires \separated(output_arr, buffer + (0 .. maxlen - 1), &head, &tail, &maxlen);

  // Default global assigns
  assigns tail, *output_arr;

  // BEHAVIOR 1: Buffer is Empty
  behavior empty:
    assumes head == tail;
    assigns \nothing;      // State must not change
    ensures \result == -1;
    ensures tail == \old(tail);

  // BEHAVIOR 2: Success
  behavior success:
    assumes head != tail;
    assigns tail, *output_arr;
    ensures \result == 0;
    
    // Data correctness
    ensures *output_arr == buffer[\old(tail)];

    // Tail wrapping logic (only applies on success)
    ensures \old(tail) + 1 == maxlen ==> tail == 0;
    ensures \old(tail) + 1 != maxlen ==> tail == \old(tail) + 1;

  complete behaviors;
  disjoint behaviors;
*/
int get(int *output_arr) {
	int next;
	if (head == tail)
		return -1; // buffer is empty

	next = tail + 1;
	if (next >= maxlen)
		next = 0;

	*output_arr = buffer[tail];
	
	tail = next;
	//@ ghost int num_elements = (head - tail + maxlen) % maxlen;
	//@ assert  num_elements >= 3 ==> (\forall integer i; 0 <= i <= num_elements - 3 ==> (buffer[(tail + i) % maxlen] + buffer[(tail + i + 1) % maxlen] == buffer[(tail + i + 2) % maxlen]));
	return 0;
}


/*@
  requires 0 <= head < maxlen;
  requires 0 <= tail < maxlen;
  requires \valid(buffer + (0 .. maxlen - 1));
  
  // Important: Tell solver global vars are not inside the buffer
  requires \separated(buffer + (0 .. maxlen - 1), &head, &tail, &maxlen);

  // Default assigns (worst case permission)
  assigns head, buffer[head];

  // BEHAVIOR 1: Buffer is Full
  behavior full:
    assumes (\let n = (head + 1 == maxlen ? 0 : head + 1); n == tail);
    assigns \nothing;      // Nothing changes if full
    ensures \result == -1;
    ensures head == \old(head); // Head stays the same

  // BEHAVIOR 2: Success
  behavior success:
    assumes !(\let n = (head + 1 == maxlen ? 0 : head + 1); n == tail);
    assigns head, buffer[\old(head)];
    ensures \result == 0;
    ensures buffer[\old(head)] == data;
    
    // Your logic, now constrained only to the success case:
    ensures \old(head) + 1 == maxlen ==> head == 0;
    ensures \old(head) + 1 != maxlen ==> head == \old(head) + 1;

  complete behaviors;
  disjoint behaviors;
*/
int put(int data) {
	int next;
	next = head + 1;
	if (next >= maxlen)
		next = 0;
	if (next == tail)
		return -1; // buffer is full
	
	buffer[head] = data;
	head = next;
	//@ ghost int num_elements = (head - tail + maxlen) % maxlen;
	//@ assert  num_elements >= 3 ==> (\forall integer i; 0 <= i <= num_elements - 3 ==> (buffer[(tail + i) % maxlen] + buffer[(tail + i + 1) % maxlen] == buffer[(tail + i + 2) % maxlen]));
	return 0;
}

//@ ghost int count;
//@ assigns buffer, head, tail, count;
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
        loop assigns i, buffer[0 .. maxlen - 1], head, a, b, count;
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

	//@ ghost int num_elements = (head - tail + maxlen) % maxlen;
	//@ assert  num_elements >= 3 ==> (\forall integer i; 0 <= i <= num_elements - 3 ==> (buffer[(tail + i) % maxlen] + buffer[(tail + i + 1) % maxlen] == buffer[(tail + i + 2) % maxlen]));

    /*@ loop invariant 0 <= j <= maxlen-1;
        loop invariant 0 <= tail <= maxlen - 1;
        loop invariant count == maxlen - 1 - j;
        loop assigns j, out[0 .. maxlen - 1], tail, count;
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
