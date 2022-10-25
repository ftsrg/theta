void reach_error();

void func(int a) {
    int x;
    if(a == 1 && x == 2) reach_error();
    x = 1;
}

int main() {
    func(0);
    func(1);
}