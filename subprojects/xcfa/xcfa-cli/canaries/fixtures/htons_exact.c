// htons and htonl reverse the bytes on a little-endian target.
extern void abort(void);
void reach_error() { abort(); }
extern unsigned short htons(unsigned short x);
extern unsigned int htonl(unsigned int x);

int main() {
  if (htons(0x1234) != 0x3412) reach_error();
  if (htonl(0x12345678u) != 0x78563412u) reach_error();
  return 0;
}
