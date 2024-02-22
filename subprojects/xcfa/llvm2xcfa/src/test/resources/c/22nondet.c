extern int __VERIFIER_nondet_int();
int main() {
    int i = 0;
    if((__VERIFIER_nondet_int() % 2) != 0) {
        i = 1;
    } else {
        i = 2;
    }
    if(i==2) reach_error();
}