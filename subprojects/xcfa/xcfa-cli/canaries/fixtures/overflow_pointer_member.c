// A pointer sum is not signed integer arithmetic. `&p->dev` and `p->dev.data` on a pointer
// with an unconstrained value (an uninitialized local, as in the LDV environment models) must
// not report an overflow.
extern int __VERIFIER_nondet_int(void);

struct device {
  void *data;
  int id;
};
struct platform_device {
  const char *name;
  int id;
  struct device dev;
};

void *get_data(struct device *d) { return d->data; }

int main() {
  struct platform_device *pdev;
  if (__VERIFIER_nondet_int()) {
    void *pdata = pdev->dev.data;
    void *other = get_data(&pdev->dev);
    return pdata == other;
  }
  return 0;
}
