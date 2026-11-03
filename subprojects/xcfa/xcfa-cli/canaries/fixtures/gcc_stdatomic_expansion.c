// What `gcc -E` makes of <stdatomic.h>: each C11 operation becomes a statement expression over an
// `__auto_type` pointer and a `typeof((void)0, *p)` temporary, handed to the generic `__atomic_*`
// builtins by pointer. Neither `__auto_type` nor a comma expression inside typeof used to parse.
extern void abort(void);
void reach_error(){ abort(); }

typedef enum
  {
    memory_order_relaxed = 0,
    memory_order_consume = 1,
    memory_order_acquire = 2,
    memory_order_release = 3,
    memory_order_acq_rel = 4,
    memory_order_seq_cst = 5
  } memory_order;
typedef _Atomic long atomic_long;

atomic_long x;

int main(void) {
  long expected = 3;
  /* atomic_init(&x, 0); atomic_store(&x, 1); atomic_load(&x) */
  __extension__ ({ __auto_type __atomic_store_ptr = (&x); __typeof__ ((void)0, *__atomic_store_ptr) __atomic_store_tmp = (0); __atomic_store (__atomic_store_ptr, &__atomic_store_tmp, (0)); });
  __extension__ ({ __auto_type __atomic_store_ptr = (&x); __typeof__ ((void)0, *__atomic_store_ptr) __atomic_store_tmp = (1); __atomic_store (__atomic_store_ptr, &__atomic_store_tmp, (5)); });
  if (__extension__ ({ __auto_type __atomic_load_ptr = (&x); __typeof__ ((void)0, *__atomic_load_ptr) __atomic_load_tmp; __atomic_load (__atomic_load_ptr, &__atomic_load_tmp, (5)); __atomic_load_tmp; }) != 1) reach_error();
  /* atomic_exchange(&x, 2); atomic_fetch_add(&x, 1) */
  if (__extension__ ({ __auto_type __atomic_exchange_ptr = (&x); __typeof__ ((void)0, *__atomic_exchange_ptr) __atomic_exchange_val = (2); __typeof__ ((void)0, *__atomic_exchange_ptr) __atomic_exchange_tmp; __atomic_exchange (__atomic_exchange_ptr, &__atomic_exchange_val, &__atomic_exchange_tmp, (5)); __atomic_exchange_tmp; }) != 1) reach_error();
  if (__atomic_fetch_add ((&x), (1), 5) != 2) reach_error();
  /* atomic_compare_exchange_strong(&x, &expected, 7) succeeds, then _weak(.., 9) fails */
  if (!__extension__ ({ __auto_type __atomic_compare_exchange_ptr = (&x); __typeof__ ((void)0, *__atomic_compare_exchange_ptr) __atomic_compare_exchange_tmp = (7); __atomic_compare_exchange (__atomic_compare_exchange_ptr, (&expected), &__atomic_compare_exchange_tmp, 0, (5), (5)); })) reach_error();
  if (__extension__ ({ __auto_type __atomic_compare_exchange_ptr = (&x); __typeof__ ((void)0, *__atomic_compare_exchange_ptr) __atomic_compare_exchange_tmp = (9); __atomic_compare_exchange (__atomic_compare_exchange_ptr, (&expected), &__atomic_compare_exchange_tmp, 1, (5), (5)); })) reach_error();
  if (expected != 7) reach_error();
  __atomic_thread_fence (memory_order_seq_cst);
  return 0;
}
