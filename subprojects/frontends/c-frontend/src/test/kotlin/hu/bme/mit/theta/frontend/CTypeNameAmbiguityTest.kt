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
package hu.bme.mit.theta.frontend

import hu.bme.mit.theta.c.frontend.dsl.gen.CLexer
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.tree.ParseTree
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertNotNull
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * `(a) * b` is a multiplication if `a` names a variable and a cast if it names a type -- and
 * nothing in the token stream says which. C settles it with a symbol table; the parser is given one
 * (its `typedefNames`), and these tests pin what it does with it.
 *
 * They assert the *shape of the parse tree*, not merely that parsing succeeded: the failure mode
 * this guards against is a construct silently parsing as something else, which no amount of "it
 * parsed" tells you about.
 */
class CTypeNameAmbiguityTest {

  private fun parse(source: String, vararg typedefNames: String): ParseTree {
    val parser = CParser(CommonTokenStream(CLexer(CharStreams.fromString(source))))
    parser.typedefNames.addAll(typedefNames)
    parser.permissiveTypeNames = false
    parser.errorHandler = BailErrorStrategy()
    return parser.compilationUnit()
  }

  private fun <T : ParseTree> ParseTree.find(type: Class<T>): T? {
    if (type.isInstance(this)) return type.cast(this)
    for (i in 0 until childCount) {
      getChild(i).find(type)?.let {
        return it
      }
    }
    return null
  }

  private fun ParseTree.hasCast() = find(CParser.CastExpressionCastContext::class.java) != null

  /**
   * Every multiplicative operator in the tree; `int a = 6;` also parses through that rule, with
   * none.
   */
  private fun ParseTree.multiplicativeSigns(): List<String> {
    val signs = mutableListOf<String>()
    fun walk(node: ParseTree) {
      if (node is CParser.MultiplicativeExpressionContext) {
        node.signs.forEach { signs.add(it.text) }
      }
      for (i in 0 until node.childCount) walk(node.getChild(i))
    }
    walk(this)
    return signs
  }

  private fun body(statement: String, decls: String = "") =
    "$decls int main() { $statement return 0; }"

  // --- (expr) vs (type) --------------------------------------------------------------------

  @Test
  fun `parenthesized variable times another is a multiplication`() {
    val tree = parse(body("int a = 6; int b = 7; int c = (a) * b;"))
    assertFalse(tree.hasCast(), "(a) * b must not be a cast when a is a variable")
    assertTrue(tree.multiplicativeSigns().contains("*"))
  }

  @Test
  fun `parenthesized type name times another is a cast of a dereference`() {
    val tree = parse(body("int c = (a) * b;", "typedef int a;"), "a")
    assertTrue(tree.hasCast(), "(a) * b must be a cast when a is a type")
  }

  @Test
  fun `the same name means different things in the two roles`() {
    // `t` is a type; `v` is not. Identical token shapes, opposite parses.
    val asType = parse(body("int c = (t) * p;", "typedef int t; int *p;"), "t")
    val asValue = parse(body("int v = 2; int p = 3; int c = (v) * p;"))
    assertTrue(asType.hasCast())
    assertFalse(asValue.hasCast())
  }

  @Test
  fun `unary signs after a parenthesized value are binary operators`() {
    for (op in listOf("-", "+", "&")) {
      val tree = parse(body("int a = 6; int b = 7; int c = (a) $op b;"))
      assertFalse(tree.hasCast(), "(a) $op b must not be a cast when a is a variable")
    }
  }

  @Test
  fun `unary signs after a parenthesized type are casts`() {
    for (op in listOf("-", "+")) {
      val tree = parse(body("int b = 7; int c = (t) $op b;", "typedef int t;"), "t")
      assertTrue(tree.hasCast(), "(t) $op b must be a cast when t is a type")
    }
  }

  @Test
  fun `a call through a parenthesized function is not a cast`() {
    val tree = parse(body("int r = (f)(1);", "int f(int x) { return x; }"))
    assertFalse(tree.hasCast(), "(f)(1) is a call when f is a function")
  }

  @Test
  fun `a parenthesized type applied to a parenthesized value is a cast`() {
    val tree = parse(body("int b = 7; int c = (t)(b);", "typedef int t;"), "t")
    assertTrue(tree.hasCast())
  }

  @Test
  fun `built-in type names are casts without being typedefs`() {
    val tree = parse(body("long b = 7; int c = (unsigned int) b;"))
    assertTrue(tree.hasCast())
  }

  @Test
  fun `a comma expression in parentheses is not a cast`() {
    val tree = parse(body("int a = 1; int b = 2; int c = (a, b) * 2;"))
    assertFalse(tree.hasCast())
  }

  // --- `T * p;` inside a block: declaration or multiplication? ------------------------------

  private fun ParseTree.hasBlockDeclaration() =
    find(CParser.BodyDeclarationContext::class.java) != null

  @Test
  fun `a pointer declaration of a typedef'd type is a declaration, not a multiplication`() {
    // The bug this guards: `blockItem` lists `statement` before `declaration`, and ANTLR settles an
    // ambiguity by alternative order -- so `S *p;` became a multiplication whose result is thrown
    // away, the variable was never declared, and `S` reached the expression visitor as a *value*
    // ("No such variable or macro: S"). C says the opposite: a block item that can be read as a
    // declaration is one.
    val tree = parse(body("S *p; p = 0;", "typedef int S;"), "S")
    assertTrue(tree.hasBlockDeclaration(), "`S *p;` must declare p when S is a type")
    assertFalse(tree.multiplicativeSigns().contains("*"), "it is not a multiplication")
  }

  @Test
  fun `the same text is a multiplication when the name is a variable`() {
    // Identical token shapes, opposite parses -- the whole point of knowing the type names.
    val tree = parse(body("int s = 2; int p = 3; s * p;"))
    assertTrue(
      tree.multiplicativeSigns().contains("*"),
      "`s * p;` is a multiplication when s is a variable",
    )
  }

  @Test
  fun `an ordinary call is not turned into a declaration`() {
    // `f(x);` matches `declarationSpecifiers initDeclarator` too -- "declare x of type f" -- if any
    // identifier may name a type. It must not, when f is merely a function.
    val tree = parse(body("f(1);", "void f(int q) {}"))
    assertFalse(tree.hasBlockDeclaration(), "`f(1);` is a call, not a declaration")
  }

  @Test
  fun `a label keeps working even when its name is also a type`() {
    // `L:` is a labelled statement, not a declaration, whatever else L may name.
    val tree = parse(body("int i = 0; L: i++; if (i < 2) goto L;", "typedef int L;"), "L")
    assertNotNull(
      tree.find(CParser.LabeledStatementContext::class.java),
      "`L:` must stay a label when L is also a typedef name",
    )
  }

  @Test
  fun `a declaration of a built-in pointer type still parses as a declaration`() {
    // This one never broke -- a keyword cannot begin an expression -- but it must stay that way.
    val tree = parse(body("int *q; q = 0;"))
    assertTrue(tree.hasBlockDeclaration())
  }

  // --- declarations ------------------------------------------------------------------------

  @Test
  fun `a function declared with a bare typedef parameter is a function, not two variables`() {
    // The bug this whole change exists for: `void *malloc(size_t);` used to parse as declarations
    // of two *variables*, `malloc` (taking `size_t` for a type name) and `size_t`.
    val tree = parse("typedef unsigned long size_t; void *malloc(size_t);", "size_t")
    val funcDecl = tree.find(CParser.DirectDeclaratorFunctionDeclContext::class.java)
    assertNotNull(funcDecl, "malloc(size_t) must be a function declarator")
    assertTrue(funcDecl!!.text.startsWith("malloc"))
  }

  @Test
  fun `a named typedef parameter parses the same way`() {
    val tree = parse("typedef unsigned long size_t; void *malloc(size_t n);", "size_t")
    val funcDecl = tree.find(CParser.DirectDeclaratorFunctionDeclContext::class.java)
    assertNotNull(funcDecl)
    assertTrue(funcDecl!!.text.startsWith("malloc"))
  }

  @Test
  fun `an unknown name in parameter position does not make the declaration a function pointer`() {
    // `notatype` is not a typedef, so this is not a valid declaration; it must not silently parse
    // into something else.
    assertThrowsAnything { parse("void *f(notatype);") }
  }

  // --- sizeof ------------------------------------------------------------------------------

  @Test
  fun `sizeof of a type name reads as a type`() {
    val tree = parse(body("unsigned long s = sizeof(t);", "typedef int t;"), "t")
    assertNotNull(tree.find(CParser.TypeNameContext::class.java), "sizeof(t) must take a type")
  }

  @Test
  fun `sizeof of a variable reads as an expression`() {
    val tree = parse(body("int a = 1; unsigned long s = sizeof(a);"))
    assertNull(
      tree.find(CParser.TypeNameContext::class.java),
      "sizeof(a) must take an expression when a is a variable",
    )
  }

  // --- a `for`'s first clause: declaration or expression? ------------------------------------

  /** Whether the `for`'s first clause was taken as a declaration. */
  private fun forInitDeclares(source: String, vararg typedefNames: String) =
    parse(source, *typedefNames).find(CParser.ForDeclarationContext::class.java) != null

  @Test
  fun `a for-init that assigns through a pointer is an expression, not a declaration`() {
    // `typeSpecifierPointer` makes its type specifier optional, so a bare `*` matches a declaration
    // specifier on its own -- and `forDeclaration` is the first alternative. Unguarded, this
    // declared a fresh, null `p` scoped to the loop, shadowing the real one: every `*p` in the body
    // then dereferenced NULL, and a safe program was reported as an invalid dereference.
    assertFalse(
      forInitDeclares("void f(int *p) { for (*p = 0; *p < 10; (*p)++) { } }"),
      "`for (*p = 0; ...)` assigns through p; it declares nothing",
    )
  }

  @Test
  fun `a for-init that really declares still declares`() {
    assertTrue(
      forInitDeclares("void f(void) { for (int i = 0; i < 10; i++) { } }"),
      "`for (int i = 0; ...)` declares i",
    )
    // The case the optional type specifier exists for: a pointer declaration must still be one.
    assertTrue(
      forInitDeclares("void f(int *q) { for (int *p = q; p; p++) { } }"),
      "`for (int *p = q; ...)` declares p",
    )
    assertTrue(
      forInitDeclares("void f(myptr q) { for (myptr p = q; p; p++) { } }", "myptr"),
      "`for (myptr p = q; ...)` declares p when myptr is a typedef",
    )
  }

  @Test
  fun `a for-init that is a plain assignment or empty declares nothing`() {
    assertFalse(
      forInitDeclares("void f(void) { int i; for (i = 0; i < 10; i++) { } }"),
      "`for (i = 0; ...)` assigns to i; it declares nothing",
    )
    assertFalse(forInitDeclares("void f(void) { for (;;) { } }"), "`for (;;)` declares nothing")
  }

  // --- parenthesized pointer declarators in a cast type ------------------------------------

  /** The number of stars in a `TYPE (*...)(args)` cast type, or null if there is no such cast. */
  private fun ParseTree.functionPointerStars(): Int? =
    find(CParser.TypeSpecifierFunctionPointerContext::class.java)?.pointer()?.stars?.size

  @Test
  fun `a cast to a single function pointer is one pointer level`() {
    // The case that always worked: it must keep parsing to exactly one level.
    val tree = parse(body("int c = (int (*)(int)) p;"))
    assertTrue(tree.hasCast(), "(int (*)(int))p is a cast")
    assertEquals(1, tree.functionPointerStars(), "(int (*)(int)) has one star")
  }

  @Test
  fun `a cast to a pointer-to-function-pointer carries two levels`() {
    // CIL writes `*((int (**)(args))p) = &f` to store a function's address through a
    // pointer-to-function-pointer; the `(**)` must parse and carry two pointer levels, not one.
    val tree = parse(body("int c = *((int (**)(int)) p);"))
    assertTrue(tree.hasCast(), "(int (**)(int))p is a cast")
    assertEquals(2, tree.functionPointerStars(), "(int (**)(int)) has two stars")
  }

  @Test
  fun `a three-star function pointer cast carries three levels`() {
    val tree = parse(body("int c = ((int (***)(void)) 0) != 0;"))
    assertTrue(tree.hasCast())
    assertEquals(3, tree.functionPointerStars())
  }

  // --- the permissive fallback -------------------------------------------------------------

  @Test
  fun `the permissive parser still takes any identifier for a type`() {
    // The fallback used when the type-aware parse fails: it must behave exactly as the parser did
    // before it knew about typedefs, so that nothing which parses today can start failing.
    val parser = CParser(CommonTokenStream(CLexer(CharStreams.fromString("void *f(notatype);"))))
    parser.errorHandler = BailErrorStrategy()
    parser.compilationUnit() // permissiveTypeNames defaults to true: must not throw
  }

  private fun assertThrowsAnything(block: () -> Unit) {
    try {
      block()
    } catch (e: Exception) {
      return
    }
    throw AssertionError("expected the parse to fail")
  }
}
