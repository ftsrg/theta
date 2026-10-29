// Under the bytes model an object's recorded size is its byte size, the unit accesses are bounded
// in: the last member of a static struct and the last element of a stack array are in bounds.
struct s { char c; int k; long l; };
struct s gs;

int main(void) {
  long la[2];
  gs.l = 1;
  la[1] = 2;
  return 0;
}
