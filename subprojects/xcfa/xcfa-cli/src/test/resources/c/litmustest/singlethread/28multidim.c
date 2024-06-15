void reach_error(){}

int a[2] = {0, 0};
int b[2] = {0, 0};

int main() {
    int k;
    if(k >= 0 && k < 2) {
        a[k] = 1;
        if(b[k] == 1) {
            reach_error();
        }
    }

}