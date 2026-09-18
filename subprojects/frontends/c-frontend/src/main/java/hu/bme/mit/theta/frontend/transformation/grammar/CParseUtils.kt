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
package hu.bme.mit.theta.frontend.transformation.grammar

import hu.bme.mit.theta.c.frontend.dsl.gen.CLexer
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser
import hu.bme.mit.theta.frontend.stdlib.headerContent
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.tree.ParseTree

/**
 * Parses C, telling type names apart from ordinary identifiers.
 *
 * The grammar cannot do that on its own: `typedefName` is just `Identifier`, so *any* name may
 * start a type. That is what makes `(a) * b` ambiguous (a cast of a dereference, or a
 * multiplication?), and what makes `void *malloc(size_t);` parse as a declaration of two
 * *variables* -- `malloc` swallowed into the specifiers as a type name, and `size_t` left over as a
 * parenthesized declarator -- rather than as a function.
 *
 * C resolves this with a symbol table, so we make one: a first pass parses the file exactly as
 * before (every identifier may be a type name) purely to harvest its typedef names, and the real
 * parse then accepts only those as types.
 *
 * The first pass must tolerate errors, since the files this is meant to fix are precisely the ones
 * that fail to parse today. The **second one must not**: if the type-aware parse cannot read the
 * file, that is the answer. There used to be a fallback here that re-parsed permissively, so that
 * no file which parsed before could start failing -- but a fallback that quietly succeeds also
 * hides every bug in the pass it is covering for. It masked a collector bug that sent *19% of
 * files* down the old, wrong path, where none of the type-aware work reached them at all, and
 * nothing said so. A parse that fails loudly is worth more than one that lies quietly.
 */
fun parseTypeAware(input: CharStream): CParser.CompilationUnitContext =
  parseC(input, collectTypedefNames(input))

/** The real parse: an identifier is a type name only if it was actually `typedef`'d. */
private fun parseC(input: CharStream, typedefNames: Set<String>): CParser.CompilationUnitContext {
  input.seek(0)
  val parser = CParser(CommonTokenStream(CLexer(input)))
  parser.typedefNames.addAll(typedefNames)
  parser.permissiveTypeNames = false
  parser.errorHandler = BailErrorStrategy()
  return parser.compilationUnit()
}

/**
 * The typedef names of the translation unit, from a permissive parse that tolerates errors.
 *
 * The names are read straight off the parse tree. Running the frontend's own visitors here would be
 * a mistake: they have side effects (registering struct tags, writing `cType` metadata into the
 * shared ParseContext), and running them twice over the same file corrupts the real parse.
 */
fun collectTypedefNames(input: CharStream): Set<String> {
  val names = LinkedHashSet<String>()
  input.seek(0)
  collectTypedefNamesFrom(input, names)
  return names
}

/** Harvests one translation unit's typedef names, following any `#include` it names. */
private fun collectTypedefNamesFrom(input: CharStream, names: MutableSet<String>) {
  val parser = CParser(CommonTokenStream(CLexer(input)))
  parser.removeErrorListeners() // a file that does not parse still tells us its typedefs, and those
  // names are often exactly what lets the *real* parse of it succeed; complain about it later
  val tree =
    try {
      parser.compilationUnit()
    } catch (e: Exception) {
      return
    }
  tree.collectTypedefNamesInto(names)
}

private fun ParseTree.collectTypedefNamesInto(names: MutableSet<String>) {
  // A header's typedefs are the program's typedefs. The include is only *expanded* much later, when
  // the visitors run, but the names have to be known now, while the file is being parsed: without
  // `pthread_mutex_t` in hand, `pthread_mutex_t mutex;` reads as a multiplication and the file does
  // not parse at all. (Headers include headers, so this recurses -- the name set is shared and
  // terminates on the finite set of headers we carry.)
  if (this is CParser.IncludeDirectiveContext) {
    headerContent(text)?.let { collectTypedefNamesFrom(CharStreams.fromString(it), names) }
  }
  if (this is CParser.DeclarationContext && isTypedef()) {
    val initDeclarators = initDeclaratorList()?.initDeclarator()
    if (initDeclarators.isNullOrEmpty()) {
      // With every identifier taken for a type name, the declared name is swallowed into the
      // specifier list (`typedef unsigned long size_t;` looks like three type specifiers). It is
      // the
      // last *type name* there -- not the last identifier, which in
      // `typedef struct {...} __pthread_unwind_buf_t __attribute__ ((__aligned__));`
      // is the attribute's (`__aligned__`), leaving the type undeclared and every later use of it
      // unparseable.
      declarationSpecifiers()?.lastTypeName()?.let(names::add)
    } else {
      initDeclarators.forEach { it.declarator()?.declaredName()?.let(names::add) }
      // `typedef void f_t(param_t);` reads here the way `void *malloc(size_t);` famously does:
      // `f_t` is swallowed into the specifiers as a type name and the *parameter* is left over
      // as a parenthesized declarator -- so the loop above just registered `param_t`, not `f_t`.
      // In that shape the declared name is the specifiers' last type name.
      if (initDeclarators.size == 1 && initDeclarators[0].declarator().isParenthesizedBareName()) {
        declarationSpecifiers()?.lastTypeName()?.let(names::add)
      }
    }
  }
  for (i in 0 until childCount) getChild(i).collectTypedefNamesInto(names)
}

/** A declarator that is nothing but `( Identifier )` -- the leftover parameter of the mis-parse. */
private fun CParser.DeclaratorContext?.isParenthesizedBareName(): Boolean {
  if (this?.pointer() != null) return false
  val braces = this?.directDeclarator() as? CParser.DirectDeclaratorBracesContext ?: return false
  val inner = braces.declarator() ?: return false
  return inner.pointer() == null && inner.directDeclarator() is CParser.DirectDeclaratorIdContext
}

private fun CParser.DeclarationContext.isTypedef() =
  declarationSpecifiers()?.declarationSpecifier()?.any { it.text == "typedef" } == true

/**
 * The name a declarator declares: its innermost identifier, e.g. `handler` in `(*handler)(int)`.
 */
private fun ParseTree.declaredName(): String? {
  if (this is CParser.DirectDeclaratorIdContext) return text
  for (i in 0 until childCount) {
    getChild(i).declaredName()?.let {
      return it
    }
  }
  return null
}

/**
 * The last name used as a *type* here; a struct's own members come before it, an attribute after.
 */
private fun ParseTree.lastTypeName(): String? {
  if (this is CParser.TypedefNameContext) return text
  for (i in childCount - 1 downTo 0) {
    getChild(i).lastTypeName()?.let {
      return it
    }
  }
  return null
}
