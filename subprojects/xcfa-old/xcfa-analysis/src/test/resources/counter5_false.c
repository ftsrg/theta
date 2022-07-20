void reach_error(){}
void assert(int c) { if(!c) reach_error(); }
int main() {
    int x = 6;
    while(x < 5) {
        x++;
    }
    assert(x < 5);
}