int main() {
    int p;
    int a;
    p = 13;
    a = 1;

    while (a < 10) {
        while (p < 50) {
            if(p == 13) {
                p = 31;
            } else {
                p = 13;
            }
        }
        a = 10;
    }

    return 0;
}
