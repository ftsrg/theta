int imglobal = 2;
int glob2;
int glob3 = 11;
char glob4 = 'a';

int adder(int a, int b) {
    int c = a;
    int d = b;
    int glob2 = glob3;
    glob3 = 5;
    glob3 = 10;
    glob3 = 15;
    return c+d+glob3;
}

int main() {
    return adder(2,-3);
}