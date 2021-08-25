void reach_error(){}

struct A{
    int a;
    char c;
    struct {
        int a;
    } b;
};

int main() {
    struct A a;
    a.a = 3;
    a.c = 1;
    if(a.a + a.c + a.b.a < 4) reach_error();
 }