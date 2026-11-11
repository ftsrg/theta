// The Juliet connect_socket pattern with the guard of the good variant.
struct in_addr { unsigned int s_addr; };
struct sockaddr_in {
  unsigned short sin_family;
  unsigned short sin_port;
  struct in_addr sin_addr;
  unsigned char sin_zero[8];
};
struct sockaddr;
extern int socket(int domain, int type, int protocol);
extern int connect(int fd, const struct sockaddr *addr, unsigned int len);
extern long recv(int fd, void *buf, unsigned long n, int flags);
extern int close(int fd);
extern unsigned int inet_addr(const char *cp);
extern unsigned short htons(unsigned short x);
extern int atoi(const char *s);

// global, so it is zero without a call that forces the bytes memory model
struct sockaddr_in service;

int main() {
  int data = 0;
  char inputBuffer[6];
  int s = socket(2, 1, 6);
  do {
    if (s == -1) break;
    service.sin_family = 2;
    service.sin_addr.s_addr = inet_addr("127.0.0.1");
    service.sin_port = htons(27015);
    if (connect(s, (struct sockaddr *)&service, sizeof(service)) == -1) break;
    long r = recv(s, inputBuffer, 5, 0);
    if (r == -1 || r == 0) break;
    inputBuffer[r] = '\0';
    data = atoi(inputBuffer);
  } while (0);
  if (s != -1) close(s);
  if (data < 2000 && data > -2000) return data * 1000000;
  return 0;
}
