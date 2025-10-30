void reach_error();

struct object {
    int attr;
};

void ptraccess(struct object* obj) {
    if(obj->attr) reach_error();
}

int main() {
    struct object obj = { 0 };
    ptraccess(&obj);
}