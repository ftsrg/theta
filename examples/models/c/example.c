#include <stdio.h>
#include <stdlib.h>

extern int reach_error();

int main() {
    int x = 0;
    for (int i = 0; i < 5; ++i) x += i;
    if (x == 10) {
        printf("Reached target value: %d\n", x);
    } else {
        printf("Unexpected value: %d\n", x);
        reach_error();
    }
    return 0;
}
