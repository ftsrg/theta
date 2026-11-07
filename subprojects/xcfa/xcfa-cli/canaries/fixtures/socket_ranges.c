// The socket calls return -1 or a valid result (POSIX), nothing else.
extern void abort(void);
void reach_error() { abort(); }
struct sockaddr { unsigned short sa_family; char sa_data[14]; };
extern int socket(int domain, int type, int protocol);
extern int connect(int fd, const struct sockaddr *addr, unsigned int len);
extern int close(int fd);

int main() {
  struct sockaddr addr = {0};
  int s = socket(2, 1, 6);
  if (s < -1) reach_error();
  if (s == -1) return 0;
  int c = connect(s, &addr, sizeof(addr));
  if (c != 0 && c != -1) reach_error();
  if (close(s) > 0) reach_error();
  return 0;
}
