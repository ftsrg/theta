void reach_error() {}
void *malloc(unsigned long);

struct Node {
    int v;
    struct Node *next;
};

int main() {
    int *buf = (int *) malloc(3 * sizeof(int));
    if (!buf) return 0;

    int *p = &buf[1];
    *(&buf[0]) = 11;
    *p = 22;
    *(&buf[2]) = 33;

    int **pp = &p;
    *(&(**pp)) = 44;
    if (buf[1] != 44) reach_error();

    struct Node *n = (struct Node *) malloc(sizeof(int));
    if (!n) return 0;

    n->v = 5;
    n->next = 0;

    int *pv = &(n->v);
    *(&n->v) = 55;

    if (*pv != 55) reach_error();

    return 0;
}
