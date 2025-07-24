int f(int x) {
    return x - 1;
}

int fp(int x) {
    return x + 1;
}

int main() {
    int x;
    x = f(x) - fp(x);
    x = f(x) - fp(x);
    x = f(x) - fp(x);
    if(x == -2) reach_error();
}