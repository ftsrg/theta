extern unsigned int __VERIFIER_nondet_uint();
int main() {
    int i = 0;
    do{
        unsigned int add = __VERIFIER_nondet_uint();
        switch(add) {
            case 0:
                break;
            case 1:
                i += add;
                break;
            default:
                i += 1;
                break;
        }
        if ( i == 5) continue;
        if ( i == 11) break;
    } while(i < 10);
    if(i < 10) reach_error();
}