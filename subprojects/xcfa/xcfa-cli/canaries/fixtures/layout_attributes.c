// batch 53: layout attributes and unnamed bitfields survive the frontend.
// The offsets they imply are checked by ObjectLayoutFromSourceTest against gcc; this fixture
// guards the parse path those changes touched (TypeVisitor's specifier walk, the declarator's
// gcc extensions, and unnamed bitfields now coming back as nameless declarations rather than
// null). Every shape below appears in the ldv/TDX headers.
struct Packed { char a; int b; } __attribute__((packed));
struct Aligned { char a; int b; } __attribute__((aligned(16)));
struct Both { char a; int b; } __attribute__((packed, aligned(8)));
struct MemberAligned { char a; int b __attribute__((aligned(8))); };
struct __attribute__((packed)) LeadingAttr { char a; int b; };
struct Padded { unsigned a : 4; unsigned : 0; unsigned b : 4; };
struct Reserved { char a; int : 3; char b; };
struct Unnamed { int x; int : 0; };

struct Packed p;
struct Aligned al;
struct Both bo;
struct MemberAligned ma;
struct LeadingAttr la;
struct Padded pd;
struct Reserved rs;
struct Unnamed un;

int main() {
  p.a = 1;
  al.b = 2;
  bo.a = 3;
  ma.b = 4;
  la.b = 5;
  pd.a = 6;
  pd.b = 7;
  rs.b = 8;
  un.x = 9;
  return (p.a != 1) + (al.b != 2) + (bo.a != 3) + (ma.b != 4) + (la.b != 5) + (pd.a != 6) +
         (pd.b != 7) + (rs.b != 8) + (un.x != 9);
}
