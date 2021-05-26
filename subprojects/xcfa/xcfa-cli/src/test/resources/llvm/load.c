int main()
{
    volatile int i = 0; //i:=0
    int j = i + 1;//j:=i+1
    i = 1;//i:=1
    j = j + i;//j:=j+i
    i = 2;//i:=2
    return j + 2;//main_ret:=j+2
}