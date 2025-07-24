void reach_error(){}
extern char __VERIFIER_nondet_char();
int main() {
    int i = 0;
    if(__VERIFIER_nondet_char() % 2) {
        i = 1;
    } else {
        i = 2;
    }
    if(i==2) reach_error();
}