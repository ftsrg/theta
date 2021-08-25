void reach_error(){}
int main() {
    int a = 12;
    unsigned int b = a;
    long c = b;
    unsigned long long d = c;
    if(d > 15) reach_error();
}