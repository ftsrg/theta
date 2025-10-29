void reach_error(){}

void f() {
    int a = 1;
    if(a) reach_error();
}

int main() {
    f();
}