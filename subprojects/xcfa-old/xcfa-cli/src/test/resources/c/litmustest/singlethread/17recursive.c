void reach_error(){}

int fibonacci(int i) {
    if(i == 0) return 0;
    else if(i == 1) return 1;
    else return fibonacci(i-1) + fibonacci(i-2);
}

int main() {
    if(fibonacci(12) != 143) reach_error();
}