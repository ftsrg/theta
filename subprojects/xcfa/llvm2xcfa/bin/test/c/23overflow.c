extern int __VERIFIER_nondet_int();
void reach_error();
int main() {
    int i = __VERIFIER_nondet_int();
    i = i * 2;
    if(i == 1) reach_error();
}