// strerror gives a fresh string: its characters are made up, so they are recorded.
extern int __VERIFIER_nondet_int(void);
extern char *strerror(int errnum);

int main() {
  char *m = strerror(__VERIFIER_nondet_int());
  return m[127] + m[0];
}
