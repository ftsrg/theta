/* Multi-TU test: file A defines helper_a, calls helper_b from file B */
int helper_a(int x) {
    return x + 1;
}

int test_cross_file_call_a() {
    int y = helper_b(5);
    return y;
}
