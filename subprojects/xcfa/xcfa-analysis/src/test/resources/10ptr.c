void reach_error(){}

int main() {
    int a = 110;
    int *b = &a;
    char *c = (char*)b;
    a = 90;
    char d = *c;
    if(d > 100) reach_error();
    *b = 120;
    d = *c;
    if(d > 100) reach_error();
 }