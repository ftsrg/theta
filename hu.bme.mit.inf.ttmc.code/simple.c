
int main(void)
{
	int x, y = 0, z = 0;

	for (x = 0; x < 3; x++) {
		y = ++z;
	}

	x++;

	assert(!(x < 0));

	return 0;
}
