
int gcd(int a, int b) {
	int c = 0;
	while (a != 0) {
		c = a;
		a = b % a;
		b = c;
	}

	return b;
}

int main() {

	int g = gcd(15, 3);
	assert(g == 3);

}
