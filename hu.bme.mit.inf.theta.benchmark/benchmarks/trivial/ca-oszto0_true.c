int main() {
	int a = 15;
	int vanoszto = 0;
	int i = 2;
	int oszto = 0;

	while (!vanoszto && i < a) {
		if (a % i == 0) {
			vanoszto = 1;
			oszto = i;
		}

		i += 1;
	}

	assert(vanoszto);
	assert(oszto == 3);

	return 0;
}
