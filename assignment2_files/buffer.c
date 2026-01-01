int* buffer;
int head = 0;
int tail = 0;
int const maxlen = 4;


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
