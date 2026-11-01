extern void reach_error();

extern unsigned int __VERIFIER_nondet_uint();

int main() {
  int sn=0;
  unsigned int x=0;
  while(1){
      if (x<10) {
          sn = sn + (2);
      }
      x++;
      if (!(sn==x*(2) || sn == 0)) reach_error();
  }
}
