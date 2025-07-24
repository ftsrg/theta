void reach_error(){}

struct A{
    int a;
    char c;
    struct {
        int a;
    } b;
};

struct A structs[1];

void f(struct A* a_ptr) {
    a_ptr->a = structs[0].a + 1; // this is .a++
}

void g(struct A a_val) {
    a_val.a = structs[0].a + 1; // this is .a++, but local only
}

struct A* h() {
    return structs;
}

int main() {
    if(structs[0].a + structs[0].c + structs[0].b.a != 0) {
        reach_error(); // global vars should be initialized to 0, even nested ones
    }
    f(&(structs[0]));
    if(structs[0].a != 1) {
        reach_error(); // .a++ in f()
    }
    g(structs[0]);
    if(structs[0].a != 1) {
        reach_error(); // .a++ in g() is local-only
    }
    g(structs[0]);
    if(structs->a != 1) { // structs->a should in theory work
        reach_error(); // .a++ in g() is still local-only
    }
    g(structs[0]);
    if(h()[0].a != 1) { // h just returns structs
        reach_error(); // .a++ in g() is still local-only
    }
    if(h()[0].a++ != 2) { // most beautiful postfix expression
        reach_error();
    }
}