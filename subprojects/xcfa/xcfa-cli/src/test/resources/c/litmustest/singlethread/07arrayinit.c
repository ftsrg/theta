void reach_error(){}

int main() {
    int x;
    int a[3] = {2, x+1, 4};
    if(a[1] > 2) reach_error();
 }