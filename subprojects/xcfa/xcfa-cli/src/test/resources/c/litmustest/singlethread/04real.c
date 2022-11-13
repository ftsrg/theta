void reach_error(){}
extern float __VERIFIER_nondet_float();
int main() {
    float f = __VERIFIER_nondet_float();
    double d = f;
    long double ld = d;
    if(ld > 0.28f && ld < 0.32f) reach_error();
}