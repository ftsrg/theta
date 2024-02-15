extern int __VERIFIER_nondet_int();
void reach_error();

int b;

void a() {
    int a = __VERIFIER_nondet_int();
    if(a) {
        b++;
        return;
    }
    b++;
}

int main() {
    a();
    if(b == 2) reach_error();
}