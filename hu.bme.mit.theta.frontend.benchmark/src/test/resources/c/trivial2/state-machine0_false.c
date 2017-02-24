
extern int nondet_int();

int calculate(int x) {
	int result = 0;

	while (1) {
		int state = x;
		int arg0, arg1;

		arg0 = nondet_int();
		arg1 = nondet_int();

		switch (state) {
			case 0:
				result = arg0 + arg1;
				state = 2;
				break;
			case 1:
				result += arg1;
				state = 0;
				break;
			case 2:
				arg0 *= 2;
				result += arg0;

				if (result < arg1 * arg0) {
					state = 1;
				} else {
					state = 7;
				}
				break;
			case 7:
				return result;
			default:
				assert(0);
				break;
		}
	}

	return -1;
}

int main() {

	int r = calculate(0);
	assert(r == 0);
}
