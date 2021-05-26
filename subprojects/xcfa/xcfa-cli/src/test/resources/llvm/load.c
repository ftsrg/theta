int main()
{
    volatile int i = 0;
    int j = i + 1;
    i = 1;
    return j + 2;
}