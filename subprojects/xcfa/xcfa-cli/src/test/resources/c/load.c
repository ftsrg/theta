extern int nondet();

int main()
{
    int i = 1;
    if(i) {
        i = nondet();
        abort();
    }
    else return 0;

}