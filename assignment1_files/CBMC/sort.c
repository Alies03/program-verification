#include <stdbool.h> 
#include <assert.h>

void two_sort(int* a, int* b) {
	if (*a > *b) {
		int c = *a;
		*a = *b;
		*b = c;
	}
}

void five_sort(int* a, int* b, int* c, int* d, int* e) {
    two_sort(a, c);
    //two_sort(b, e);
    two_sort(b, d);
    two_sort(a, b);
    two_sort(a, e);
    two_sort(c, e);
    two_sort(c, d);
    two_sort(b, c);
    two_sort(d, e);
    two_sort(c, d);
}

int main() {
	int a;
	int b;
	int c;
	int d;
	int e;

	five_sort(&a, &b, &c, &d, &e);
	
	assert(a <= b);
	assert(b <= c);
	assert(c <= d);
	assert(d <= e);

	return 0;
}