void reach_error(){}

void check_geq_110(void* param) {
    if(*(unsigned int*)param <= 110) reach_error();
}

int main() {
    float f = 0.3f;
    unsigned int all = -1;
    check_geq_110(&all);
 }