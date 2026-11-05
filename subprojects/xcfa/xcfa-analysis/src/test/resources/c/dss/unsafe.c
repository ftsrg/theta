void reach_error() {}

int main() {
  int x = 20;
  if (x < 10) {
    // ok
  } else {
    reach_error();
  }
  return 0;
}
