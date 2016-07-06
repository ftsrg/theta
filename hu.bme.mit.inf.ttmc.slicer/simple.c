int main()
{
	int sum = 0;
	int i = 1;

	if (sum == 0) {
		while (i < 11) {
			sum = sum + i;
			i = i + 1;
		}
	} else {
		sum = sum + 1;
	}

	assert(i < 100);
	assert(sum > 20);

	return 0;
}
