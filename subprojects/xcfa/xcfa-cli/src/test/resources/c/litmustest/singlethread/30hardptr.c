void reach_error(){}
extern int* malloc();
int main() {
    int *i = malloc();
    int x, y;

    i[x+2] = 1;
    i[y-2] = 2;
    if(i[x+2] == 1 && x+2==y-2) {
        reach_error();
    }
}