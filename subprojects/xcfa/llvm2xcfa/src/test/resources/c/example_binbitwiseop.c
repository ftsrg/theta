#include <stdio.h>

int main() {
    int a, b;
    scanf("%d", &a);
    scanf("%d", &b);

    int c = a / b << 2;
    int d = b >> 2;
    unsigned int e = c | d & 11;

    if( (e << 2) == 44) {
        e = e ^ c;
        e = e / c;
        e = e % a;
    }

    return (unsigned long long)(char)(e + a - b * c);
}