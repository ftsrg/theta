// DBL_EPSILON is the gap between 1.0 and the next double, 2^-52; the macro table held 2^-53, so
// 1.0 + DBL_EPSILON rounded back to 1.0. The FLT_ macros carried a C `F` suffix the value parser
// rejects, which failed the frontend.
extern void abort(void);
void reach_error(){ abort(); }

int main() {
  if (DBL_EPSILON != 0x1p-52) reach_error();
  if (1.0 + DBL_EPSILON == 1.0) reach_error();
  if (1.0 + DBL_EPSILON / 2 != 1.0) reach_error();
  if (FLT_EPSILON != 0x1p-23f) reach_error();
  if (FLT_MIN != 0x1p-126f) reach_error();
  if (FLT_MAX != 0x1.fffffep127f) reach_error();
  return 0;
}
