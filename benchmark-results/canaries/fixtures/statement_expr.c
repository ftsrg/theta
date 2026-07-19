// batch 39: gcc statement expression yields the last expression
int main() { int y = ({ int t = 4; t + 1; }); return y != 5; }
