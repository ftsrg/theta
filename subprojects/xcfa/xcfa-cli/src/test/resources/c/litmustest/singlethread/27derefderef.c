extern int* malloc(int a);

void reach_error(){}

int main() {
    int *i_ptr = malloc(sizeof(int));
    int i = __VERIFIER_nondet_int();
    int j = __VERIFIER_nondet_int();
    *i_ptr = i;
    *i_ptr = j;
    if(i != j && *i_ptr) {
        reach_error();
    }
}