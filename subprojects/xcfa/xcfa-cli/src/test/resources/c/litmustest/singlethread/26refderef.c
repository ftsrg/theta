void reach_error(){assert(0);}
extern int nondet();
void f(int* a) {
    *a = nondet();
}

int main() {
    int i = nondet();
    int j = 0;
    int *i_ptr;
    if (i % 2) {
        i_ptr = &i;
    }
    else {
        i_ptr = &j;
    }
    f(i_ptr);
    if(j != 0) {
        reach_error();
    }
}