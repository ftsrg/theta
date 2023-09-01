void reach_error(){}
float fabs(float);
float floor(float);
float round(float);
float fmax(float, float);
float fmin(float, float);
float sqrt(float);
int isnan(float);

int main() {
    float f = 12.65f;
    float f1 = fabs(f);
    float f2 = floor(f);
    float f3 = round(f);
    float f4 = fmax(f2, f3);
    float f5 = fmin(f2, f3);
    float f6 = sqrt(f);
    float f7 = isnan(f);
    f = 0.0f;
    float f8 = isnan(0.0f/0.0f);
    if(f8) reach_error();
}