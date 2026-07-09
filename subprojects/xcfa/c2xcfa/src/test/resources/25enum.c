// Enum constants must resolve to their integer values (named + anonymous,
// explicit + implicit numbering, and references to earlier constants via
// constant-foldable expressions).
extern void abort(void);
extern void reach_error(void);

enum Color { RED, GREEN, BLUE = 5, PURPLE };
enum { SOCK_STREAM = 1, SOCK_DGRAM = 2 };
enum Nums { N_A = 10, N_B = N_A + 2, N_C };

int main() {
  if (RED != 0) goto err;
  if (GREEN != 1) goto err;
  if (BLUE != 5) goto err;
  if (PURPLE != 6) goto err; // implicit, previous + 1
  if (SOCK_STREAM != 1) goto err;
  if (SOCK_DGRAM != 2) goto err;
  if (N_A != 10) goto err;
  if (N_B != 12) goto err; // N_A + 2
  if (N_C != 13) goto err; // implicit, previous + 1
  return 0;
err:
  reach_error();
  abort();
  return 1;
}
