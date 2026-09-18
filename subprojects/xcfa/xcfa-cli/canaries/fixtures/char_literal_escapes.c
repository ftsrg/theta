// Character constants used to be decoded by hand, wrongly on every axis: `'\x41'` was
// read as *octal* 41, `'\101'` as *decimal* 101, the text was lowercased first (so `'A'`
// came out as 97, not 65), and any single-letter escape -- `'\n'`, `'\t'`, `'\\'` --
// threw NumberFormatException straight out of the frontend.
extern void abort(void);
void reach_error() { abort(); }

int main() {
  if ('A' != 65 || 'a' != 97 || 'Z' != 90) reach_error();
  if ('\n' != 10 || '\t' != 9 || '\r' != 13) reach_error();
  if ('\\' != 92 || '\'' != 39 || '\"' != 34) reach_error();
  if ('\0' != 0) reach_error();
  if ('\x41' != 65 || '\x7f' != 127) reach_error();
  if ('\101' != 65 || '\012' != 10) reach_error();
  return 0;
}
