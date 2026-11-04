// Recursion is not inlined, so termination is left to the ASG abstraction, which keeps the call
// stack in its state.
int f(int n) { if (n <= 0) return 0; return f(n - 1); }
int main() { return f(10); }
