extern int reach_error();

typedef struct A{
  int i;
} _struct_a;

void f(int i) {
  _struct_a str; // nondet
  if(i == 0 && str.i) { // first invocation: str.i is not 0
    f(1);
  }
  if(i != 0 && !str.i) { // second invocation: str.i is 0
    reach_error(); // should be reachable, two instances of _struct_a exist
  }
}

int main() {
  f(0);
}
