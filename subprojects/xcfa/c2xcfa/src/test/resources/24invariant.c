void reach_error(){}

int x;

int main() {
    int i = 0;
    while(1) {
        i += 2;
        x += 3;
        int j = 0;
        if(j != 0 || i % 2 || x % 3) reach_error(); //never called

        if(i > 10) i = 0;
        if(x > 10) x = 0;
    }
}