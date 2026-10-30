// __atomic_test_and_set, __atomic_clear, the C11 atomic_flag operations and the lock-free
// queries failed in the frontend ("No such variable or macro"). An atomic_flag is a struct
// around the flag byte, so its operations must reach that byte.
#include <stdatomic.h>
extern void abort(void);
void reach_error() { abort(); }

unsigned char byte;
_Bool flag;
atomic_flag af;
long l;
atomic_int ai;

int main() {
  if (__atomic_test_and_set(&byte, 5) != 0) reach_error();
  if (byte == 0) reach_error();
  if (__atomic_test_and_set(&byte, 5) != 1) reach_error();
  __atomic_clear(&byte, 3);
  if (byte != 0) reach_error();
  if (__atomic_test_and_set(&flag, 5)) reach_error();
  if (!flag) reach_error();

  if (atomic_flag_test_and_set(&af)) reach_error();
  if (!atomic_flag_test_and_set_explicit(&af, memory_order_acquire)) reach_error();
  atomic_flag_clear(&af);
  if (atomic_flag_test_and_set(&af)) reach_error();
  atomic_flag_clear_explicit(&af, memory_order_release);
  if (atomic_flag_test_and_set(&af)) reach_error();

  if (!__atomic_always_lock_free(sizeof(int), 0)) reach_error();
  if (__atomic_always_lock_free(3, 0)) reach_error();
  if (!__atomic_is_lock_free(sizeof(long), &l)) reach_error();
  if (!atomic_is_lock_free(&ai)) reach_error();
  return 0;
}
