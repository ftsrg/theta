extern int abort();

int main()
{
    int i = 1;
    if(i) {
        return abort();
    }
    else return 0;

}