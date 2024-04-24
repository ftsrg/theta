void reach_error(){}

int* malloc(int);

int main() {
    int k=10;
    int* arr = malloc(42);

    for(int i = 0; i < k; i++) {
        arr[i] = i * 2;
    }

    for(int i = 0; i < k; i++) {
        if(arr[i] % 2) {
            reach_error();
        }
    }

}