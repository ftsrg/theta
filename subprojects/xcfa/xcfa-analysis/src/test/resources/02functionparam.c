void reach_error(){}

int f(int a) {
    return 2/a;
}

int main() {
    int a = f(1);
    if(!a) reach_error();
}