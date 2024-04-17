void reach_error(){}

int* malloc(int);

int main() {
    int* arr = malloc(42);

    for(int i = 0; i < 42; i++) {
        arr[i] = i * 2;
    }

    for(int i = 0; i < 42; i++) {
        if(arr[i] % 2) {
            reach_error();
        }
    }

}