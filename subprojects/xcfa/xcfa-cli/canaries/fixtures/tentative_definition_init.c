// A global declared before its definition is in scope from its first declaration, but its
// initializer may name globals declared only in between (the LDV driver-struct pattern). Its
// storage must exist from the first declaration, as `registry` takes its address in between.
extern void abort(void);
void reach_error() { abort(); }

struct handler {
  int id;
};
struct driver {
  const struct handler *h;
  int n;
};

static struct driver drv;                           // declared here
static struct driver *const registry[1] = {&drv};   // its address, taken in between
static int probe(void) { return drv.h->id; }        // used in between
static const struct handler user_handler = {7};     // named by the definition
static struct driver drv = {&user_handler, 1};      // defined here

int main(void) {
  if (registry[0] != &drv) reach_error();
  if (registry[0]->n != 1) reach_error();
  if (probe() != 7) reach_error();
  return 0;
}
