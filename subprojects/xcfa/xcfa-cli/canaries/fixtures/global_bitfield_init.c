// A global brace initializer of packed bitfields, under a model that addresses the storage unit
// at its byte offset: the values are spliced into the unit's bits.
extern void abort(void);
void reach_error() { abort(); }

struct flags { unsigned a : 3, b : 5; int c; };
struct flags go = {6, 9, 4};

int main(void) {
  if (go.a != 6 || go.b != 9 || go.c != 4) reach_error();
  return 0;
}
