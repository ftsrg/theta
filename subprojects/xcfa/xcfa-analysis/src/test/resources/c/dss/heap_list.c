// From sv-benchmarks list-simple/sll2c_prepend_equal.c: safe, and its loop block reads the heap
extern void *malloc(unsigned int size);
extern void abort(void);
void reach_error() {}

typedef struct node {
  struct node *next;
  int data;
} *SLL;

SLL node_create(int data) {
  SLL temp = (SLL)malloc(sizeof(struct node));
  if (temp == 0) {
    abort();
  }
  temp->next = 0;
  temp->data = data;
  return temp;
}

SLL sll_circular_create(int len, int data) {
  SLL head = node_create(data);
  SLL last = head;
  while (len > 1) {
    SLL new_head = node_create(data);
    new_head->next = head;
    head = new_head;
    len--;
  }
  last->next = head;
  return head;
}

void sll_circular_prepend(SLL *head, int data) {
  SLL new_head = node_create(data);
  if (*head == 0) {
    *head = new_head;
    new_head->next = new_head;
  } else {
    SLL last = *head;
    while (last->next != *head) {
      last = last->next;
    }
    new_head->next = *head;
    *head = new_head;
    last->next = new_head;
  }
}

int main(void) {
  const int len = 2;
  const int data = 1;
  SLL s = sll_circular_create(len, data);
  sll_circular_prepend(&s, data);
  SLL ptr = s;
  int count = 0;
  do {
    if (data != ptr->data) {
      reach_error();
    }
    ptr = ptr->next;
    count++;
  } while (ptr != s);
  if (count != 1 + len) {
    reach_error();
  }
  return 0;
}
