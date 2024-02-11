int main() {
    int a = 0;
    if(a>0) {
        a=0;
    }
    goto label;
    return 1;

    label:
        a = 3;
        return 0;
}