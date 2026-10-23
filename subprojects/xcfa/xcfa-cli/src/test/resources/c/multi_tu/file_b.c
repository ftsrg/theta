/* Multi-TU test: file B defines helper_b, calls helper_a from file A */
int helper_b(int x) {
    return x * 2;
}

int test_cross_file_call_b() {
    int y = helper_a(3);
    return y;
}
