void reach_error() {}

int main() {
    int x = 1;
    int *px = &x;
    int **ppx = &px;

    int *r1 = &x;
    int *r2 = &(*px);
    int *r3 = &(**ppx);

    *(&x) = 2;
    if (x != 2) reach_error();

    **(&px) = 3;
    if (x != 3) reach_error();

    if (*r1 != 3 || *r2 != 3 || *r3 != 3) reach_error();

    return 0;
}
