#include <stdio.h>

struct Immastruct {
    int x;
    char c;
    long lx;
};

// struct Immastruct e = {3,'a', 2};
// int arr[2] = {12,13};

int main() {
//     scanf("%d", &(e.x));

//     printf("%d", e.x);
//     printf("%d", arr[1]);

    int x;
    scanf("%d", &x);
    struct Immastruct e_loc;
    //int arr_loc[2] = {12,13};
    e_loc.x = x;
    printf("%d", e_loc.x);
    //printf("%d", arr_loc[1]);
    return 0;
}