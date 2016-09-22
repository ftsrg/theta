
int main() {
	int x = 5;
	int i = 0;
	int sum = 0;

	while (i < x) {
		sum = sum + i;
		i = i + 1;
	}

	assert(i != 0);
	assert(sum != 0);
	assert(sum == 10);
	assert(sum != 10);

}
