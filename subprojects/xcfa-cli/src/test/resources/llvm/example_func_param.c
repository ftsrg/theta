int adder(int a, int b) {
    int c = a; int d = b;
    return c+d;
}
#include <stdio.h>
int main() {
    int a, b;
    scanf("%d, %d", &a, &b);
    return adder(a,b);
}