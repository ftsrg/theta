// The other half of the fesetround refusal: selecting the mode theta *does* model must keep working
// rather than being refused wholesale. FE_TONEAREST is 0, and fesetround returns 0 for success.
extern void abort(void);
void reach_error(){ abort(); }
extern int fesetround(int);
extern int fegetround(void);
int main() {
  if (fesetround(0) != 0) reach_error();      /* FE_TONEAREST: a no-op that succeeds */
  if (fegetround() != 0) reach_error();       /* the only mode that can be in effect */
  float a = 1.0f, b = 0x1.8p-24;              /* 0.75 ulp rounds up under to-nearest */
  if (!((float)(a + b) == 0x1.000002p+0f)) reach_error();
  return 0;
}
