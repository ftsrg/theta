extern int nondet_int();

int main() {
	int lock = 0;
	int pv = nondet_int();

	if (pv % 2 == 0) {
		lock = -lock;
	}

	assert(lock != 0);
}
