
extern int nondet_int();

int main() {
	int a = nondet_int();
	int b = nondet_int();

	int c;
	while (a != 0) {
		c = a;
		a = b % a;
		b = c;
	}

	assert(b != 0);

}
