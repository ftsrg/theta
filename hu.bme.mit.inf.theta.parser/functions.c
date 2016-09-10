int min(int a, int b)
{
    if (a<b)
        return a;
    else
        return b;
}

int max(int a, int b)
{
	if (a > b)
		return a;
	else
		return b;
}

extern int nondet_int();

int main() {
	int x = nondet_int();
	int y = nondet_int();

	int a = nondet_int();
	int b = nondet_int();

	int m = min(max(x, b), y);
	int u = m * 3;


    return 0;
}
