/*
 *  Copyright 2026 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.c2xcfa

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.RequiresByteAddressedMemoryException
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.MemoryModelType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.passes.memory.UnsupportedPointerSplitException
import org.junit.jupiter.api.Assertions.assertDoesNotThrow
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.ValueSource

/**
 * Small programs that view one object both as bytes and as something else, and controls that do
 * not.
 */
class VoidPointerViewsCasesTest {

  private companion object {
    /** The refusals of [VoidPointerViews], not those of other frontend checks. */
    const val OWN = "the cell memory models cannot relate"
  }

  private val prelude =
    """
    extern void *malloc(unsigned long);
    extern void *memset(void *, int, unsigned long);
    extern void *realloc(void *, unsigned long);
    typedef unsigned char u8;
    struct N { unsigned long a; unsigned long b; };
    struct M { char c; int i; };
    struct L { struct L *next; };
    struct O { int a; struct L l; };
    struct H { u8 *buf; };
    struct V { void *data; };
    struct W { int *num; u8 *name; };
    u8 *gp;
    void setByte(void *b) { u8 *p = (u8 *) b; p[1] = 1; }
    int isZero(const void *b) { const u8 *p = (const u8 *) b; return p[1] == 0; }
    void setGlobal(void) { gp[1] = 1; }
    void *same(void *b) { return b; }
    void writeThrough(void (*f)(void *), void *b) { f(b); }
    """
      .trimIndent()

  private fun build(body: String, memoryModel: MemoryModelType = MemoryModelType.multi) {
    val parseContext = ParseContext()
    parseContext.arithmetic = ArithmeticType.bitvector
    parseContext.architecture = ArchitectureType.LP64
    parseContext.memoryModel = memoryModel
    getXcfaFromC(
      "$prelude\n$body".byteInputStream(),
      parseContext,
      false,
      XcfaProperty(ErrorDetection.ERROR_LOCATION),
      NullLogger.getInstance(),
    )
  }

  private fun refusal(body: String): RequiresByteAddressedMemoryException? =
    try {
      build(body)
      null
    } catch (e: Throwable) {
      val causes = generateSequence(e) { it.cause }.toList()
      when {
        // A later pass may fail on the construct for its own reason: this check let it through.
        causes.any { it is UnsupportedPointerSplitException } -> null
        else ->
          causes.filterIsInstance<RequiresByteAddressedMemoryException>().firstOrNull() ?: throw e
      }
    }

  @ParameterizedTest
  @ValueSource(
    strings =
      [
        "int main(void){ long x=0; setByte(&x); return x; }",
        "int main(void){ struct N n; n.a=0; setByte(&n); return n.a; }",
        "int main(void){ struct N n; memset(&n,0,sizeof(n)); return isZero(&n); }",
        "int main(void){ unsigned long a[2]; memset(a,0,sizeof(a)); return isZero(a); }",
        "int main(void){ struct N n; n.a=0; u8 *p=(u8*)(void*)&n; p[1]=1; return n.a; }",
        "int main(void){ struct N *q=(struct N*)malloc(sizeof(struct N)); if(!q) return 0; q->a=0; setByte(q); return q->a; }",
        "int main(void){ unsigned long *q=(unsigned long*)malloc(8); if(!q) return 0; *q=0; setByte(q); return *q; }",
        "int main(void){ long x=0; struct H h; h.buf=(u8*)(void*)&x; h.buf[1]=1; return x; }",
        "int main(void){ long x=0; struct H h; h.buf=(void*)&x; u8 *p=h.buf; p[1]=1; return x; }",
        "int main(void){ long x=0; gp=(u8*)(void*)&x; setGlobal(); return x; }",
        "int main(void){ long x=0; struct V v; v.data=&x; u8 *p=(u8*)v.data; p[1]=1; return x; }",
        "int main(void){ long x=0; unsigned long a=(unsigned long)&x; setByte((void*)a); return x; }",
        "int main(void){ long x=0; u8 *p=(u8*)same(&x); p[1]=1; return x; }",
        "int main(void){ long x=0; writeThrough(setByte,&x); return x; }",
        "int main(void){ struct M s; s.i=0; setByte(&s.i); return s.i; }",
        "int main(void){ long *q=(long*)malloc(8); if(!q) return 0; *q=0; u8 *p=(u8*)realloc(q,16); if(!p) return 0; p[1]=1; return 0; }",
        "int main(void){ long x=0; u8 *p=(u8*)(void*)&x; p++; *p=1; return x; }",
        "int main(int c, char **v){ long x=0; long y=0; void *t=c?(void*)&x:(void*)&y; setByte(t); return x; }",
      ]
  )
  fun mixedViewsAreRefused(body: String) {
    assertEquals(true, OWN in refusal(body)?.message.orEmpty(), "not refused: $body")
  }

  @ParameterizedTest
  @ValueSource(
    strings =
      [
        "int main(void){ u8 *p=(u8*)malloc(16); if(!p) return 0; p[3]=1; return p[3]; }",
        "int main(void){ struct M s; s.c=1; s.i=2; return s.i; }",
        "int main(void){ struct O o; o.a=5; struct L *lp=&o.l; struct O *q=(struct O*)((u8*)lp-8); return q->a; }",
        "int main(void){ int a[4]; int *p=a; p[1]=2; return a[1]; }",
        "int main(void){ struct M s; int *q=&s.i; *q=3; return s.i; }",
        "int main(void){ struct M s; struct M *q=&s; q->c=1; q->i=2; return q->i; }",
        "int main(void){ struct M s; struct M *q=&s; int *r=&q->i; *r=2; q->c=1; return s.i; }",
        "int main(void){ long x; long *q=(long*)(void*)&x; *q=1; return x; }",
        "int main(void){ struct L *a=(struct L*)malloc(sizeof(struct L)); if(!a) return 0; a->next=0; return a->next==0; }",
        "int main(void){ struct N n; memset(&n,0,sizeof(n)); return n.a==0 && n.b==0; }",
        "int main(void){ int x=0; u8 b[4]; struct W w; w.num=&x; w.name=b; *w.num=1; w.name[1]=2; return x; }",
        "int main(void){ int i=1; int a[2]; u8 b[2]; a[i]=1; b[i]=2; return a[i]+b[i]; }",
        "int main(void){ u8 b[4]; b[0]=0; u8 *p=b; while (*p) p++; return p-b; }",
        "int main(void){ int a[4]; a[0]=0; int *p=a; p++; *p=1; return a[1]; }",
      ]
  )
  fun singleViewsAreKept(body: String) {
    assertEquals(null, refusal(body)?.message?.takeIf { OWN in it }, "refused: $body")
  }

  /** The frontend refuses some of these itself, which sends them to the same retry. */
  @ParameterizedTest
  @ValueSource(
    strings =
      [
        "int main(void){ union { long l; u8 c[8]; } u; u.l=0; long *q=&u.l; u8 *p=(u8*)q; p[1]=1; return u.l; }",
        "int main(void){ union { long l; u8 c[8]; } u; u.l=0; setByte(&u.l); return u.l; }",
        "int main(void){ union { long l; u8 c[8]; } u; long *q=&u.l; *q=0; setByte(q); return u.l; }",
        "int main(void){ union { long l; int i; } u; u.l=0; setByte(&u.l); return u.l; }",
        "int main(void){ union { long l; int i; } u; u.l=0; setByte(&u); return u.l; }",
      ]
  )
  fun viewsOfAUnionMemberAreRefused(body: String) {
    assertEquals(true, refusal(body) != null, "not refused: $body")
  }

  @ParameterizedTest
  @ValueSource(strings = ["int main(void){ long x=0; setByte(&x); return x; }"])
  fun theBytesModelIsNotRefused(body: String) {
    assertDoesNotThrow { build(body, MemoryModelType.bytes) }
  }
}
