// batch 40: designated initializers place elements by position
int arr[5] = { [2] = 7, 8 };
struct P { int x; int y; };
struct P p = { .y = 3 };
int main() { return (arr[2] != 7) + (arr[3] != 8) + (p.y != 3); }
