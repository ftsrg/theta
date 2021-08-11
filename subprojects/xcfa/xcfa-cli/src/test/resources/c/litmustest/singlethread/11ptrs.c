void reach_error(){}

void check_geq_110(int* param) {
    if(*param >= 110) reach_error();
}

int main() {
    int a = 100, b = 110, c = 120;
    check_geq_110(&a);
    check_geq_110(&b);
    check_geq_110(&c);
 }