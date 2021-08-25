void reach_error(){}

extern unsigned short nondet_ushort();

int main() {
    short ush;
    long c;
    ush = nondet_ushort();
    if(ush) reach_error();
 }