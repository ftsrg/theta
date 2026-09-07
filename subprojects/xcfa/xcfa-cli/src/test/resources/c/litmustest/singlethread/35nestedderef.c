void reach_error() {}

int main() {
    int x = 10;
    int y = 20;

    int *p = &x;
    int **pp = &p;
    int ***ppp = &pp;

    int *alias_x = &(**pp);
    *(&***ppp) = 30;
    if (x != 30) reach_error();

    p = &y;

    int *alias_y = &(**pp);
    *alias_x = 31;
    *(&(**pp)) = 40;

    if (x != 31) reach_error();
    if (y != 40) reach_error();
    if (*alias_y != 40) reach_error();

    return 0;
}
