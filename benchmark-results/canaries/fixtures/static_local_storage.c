// The `static` storage-class specifier was dropped outright, so a static local became
// an ordinary one: freshly declared on every entry and re-run through its initializer
// each time. A counter never counted past one and a one-shot guard fired on every call.
extern void abort(void);
void reach_error() { abort(); }

static int fileScope = 5; // static at file scope: linkage only, still a plain global

int bump(void) {
  static int count = 0;
  count++;
  return count;
}

static int firstOnly(void) { // `static` on a function must stay a plain definition
  static int done = 0;
  if (done) return 0;
  done = 1;
  return 1;
}

int tail(void) {
  static int hist[4] = {7};
  hist[1]++;
  return hist[0] + hist[1] + hist[3];
}

int main() {
  if (bump() != 1 || bump() != 2 || bump() != 3) reach_error();
  if (firstOnly() != 1 || firstOnly() != 0) reach_error();
  if (tail() != 8 || tail() != 9) reach_error(); // hist[0]=7, hist[3]=0, hist[1] counts
  if (fileScope != 5) reach_error();
  return 0;
}
