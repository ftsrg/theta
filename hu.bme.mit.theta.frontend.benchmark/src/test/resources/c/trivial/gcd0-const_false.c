extern int nondet_int();

int main() {
	int a = 14;
	int b = 7;

	int c;
	while (a != 0) {
		c = a;
		a = b % a;
		b = c;
	}

	assert(b == 0);

}
