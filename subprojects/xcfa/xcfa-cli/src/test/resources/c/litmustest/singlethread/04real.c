void reach_error(){}

int main() {
    float f = 0.33f;
    double d = f;
    long double ld = d;
    if(ld > 0.28f && ld < 0.32f) reach_error();
}