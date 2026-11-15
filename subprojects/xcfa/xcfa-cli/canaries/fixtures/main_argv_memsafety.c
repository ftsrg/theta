// Nothing allocates what argv points to, so every access through it would be reported invalid:
// memory safety of an entry point that reads argv is refused.
int first;
int main(int argc, char *argv[]) {
  if (argc > 1) first = argv[1][0];
  return 0;
}
