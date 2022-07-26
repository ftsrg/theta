void reach_error(){}
int nondet32();

int main() {
    int a = nondet32();
    int b = nondet32();
    if(a == 1) {
        if(b == 2) {
            reach_error();
        }
    }
}