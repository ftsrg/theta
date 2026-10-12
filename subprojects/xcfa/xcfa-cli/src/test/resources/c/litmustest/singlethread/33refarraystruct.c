void reach_error() {}

struct Pair {
    int a;
    int b;
};

int main() {
    int arr[4] = {1, 2, 3, 4};
    int *p0 = &arr[0];
    int *p2 = &arr[2];

    *(&arr[1]) = 20;
    if (arr[1] != 20) reach_error();

    struct Pair s; 
    s.a = 5;
    s.b = 6;
    int *sa = &s.a;
    int *sb = &s.b;

    *(&s.a) = 50;
    *(&s.b) = 60;
    if (*sa != 50 || *sb != 60) reach_error();

    struct Pair as[2];
    as[0].a = 7;
    as[0].b = 8;
    as[1].a = 9;
    as[1].b = 10;
    int *elem = &as[1].b;
    if (*elem != 10) reach_error();

    *(&as[1].a) = 90;
    if (as[1].a != 90) reach_error();

    if (*p0 != 1 || *p2 != 3) reach_error();

    return 0;
}
