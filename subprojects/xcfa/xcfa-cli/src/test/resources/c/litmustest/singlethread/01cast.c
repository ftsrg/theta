void reach_error(){}
int nondetint();
int main() {
    int a = nondetint();
    if((char)a) reach_error();
}