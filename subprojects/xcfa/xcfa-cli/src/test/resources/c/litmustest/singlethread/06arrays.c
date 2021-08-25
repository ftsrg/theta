void reach_error(){}

int main() {
    int a[2], b[3];
    a[0] = 12;
    b[3] = a[0];
    if(b[3] > 11) reach_error();
}