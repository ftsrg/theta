// recv returns -1 or at most n bytes, so the terminator stays inside the buffer.
extern long recv(int fd, void *buf, unsigned long n, int flags);

int main() {
  char buf[14];
  long r = recv(3, buf, 13, 0);
  if (r == -1 || r == 0) return 0;
  buf[r] = 0;
  return 0;
}
