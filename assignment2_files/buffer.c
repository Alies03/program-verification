int* buffer;
int head = 0;
int tail = 0;
int const maxlen = 4;


/*@
	requires \valid(output_arr);
	requires 0 <= tail < maxlen;
	requires \valid(buffer);
	requires \valid(buffer + (0.. maxlen-1));
	assigns *output_arr;
	ensures \result == -1 ==> head == tail;
	ensures \result == 0 ==> (*output_arr == buffer[\old(tail)]);
	ensures 0 <= tail < maxlen;
	ensures \old(tail) + 1 == maxlen ==> tail == 0;
	ensures \old(tail) + 1 != maxlen ==> tail == \old(tail) + 1;
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
	return 0;
}


/*@
  requires 0 <= head < maxlen;
  requires \valid(buffer + (0 .. maxlen - 1));
  assigns head, buffer[\old(head)];
  ensures 0 <= head < maxlen;
  ensures buffer[\old(head)] == data;
  ensures \result == -1 ==> head == tail;
  ensures \old(head) + 1 == maxlen ==> head == 0;
  ensures \old(head) + 1 != maxlen ==> head == \old(head) + 1;
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
	return 0;
}


int main() {
	int data[4];
	buffer = data;
	int out[4];

	int a = 1;
	int b = 1;
	put(a);
	put(b);
	for (int i = 2; i < maxlen-1; i++) {
		int sum = a + b;
		if(put(sum)) {
			// Out of space
			return -1;
		}
		a = b;
		b = sum;
	}

	for (int j = 0; j < maxlen-1; j++) {
		if (get(&out[j])) {
			// Buffer is empty
			return -1;
		}
	}
	return 0;
}
