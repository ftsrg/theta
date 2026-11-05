// inet_addr of a literal is its address in network byte order (little-endian target).
extern void abort(void);
void reach_error() { abort(); }
extern unsigned int inet_addr(const char *cp);

int main() {
  if (inet_addr("127.0.0.1") != 0x0100007fu) reach_error();
  if (inet_addr("256.0.0.1") != 0xffffffffu) reach_error();
  return 0;
}
