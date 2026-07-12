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
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.tree.ParseTree
import org.antlr.v4.runtime.tree.TerminalNode

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
 * that fail to parse today. And if the type-aware parse fails, we fall back to the old permissive
 * one: a typedef name the first pass failed to spot would otherwise turn a file that parses today
 * into one that does not. Nothing that parses now can start failing.
 */
fun parseTypeAware(input: CharStream): CParser.CompilationUnitContext {
  val typedefNames = collectTypedefNames(input)
  return try {
    parseC(input, typedefNames)
  } catch (e: Exception) {
    parseC(input, typedefNames = null)
  }
}

/**
 * A parse with `typedefNames` as the type names, or the old any-identifier-is-a-type parse if null.
 */
private fun parseC(input: CharStream, typedefNames: Set<String>?): CParser.CompilationUnitContext {
  input.seek(0)
  val parser = CParser(CommonTokenStream(CLexer(input)))
  if (typedefNames != null) {
    parser.typedefNames.addAll(typedefNames)
    parser.permissiveTypeNames = false
  }
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
  input.seek(0)
  val parser = CParser(CommonTokenStream(CLexer(input)))
  parser.removeErrorListeners() // a file that does not parse still tells us its typedefs
  val names = LinkedHashSet<String>()
  val tree =
    try {
      parser.compilationUnit()
    } catch (e: Exception) {
      return names
    }
  tree.collectTypedefNamesInto(names)
  return names
}

private fun ParseTree.collectTypedefNamesInto(names: MutableSet<String>) {
  if (this is CParser.DeclarationContext && isTypedef()) {
    val initDeclarators = initDeclaratorList()?.initDeclarator()
    if (initDeclarators.isNullOrEmpty()) {
      // With every identifier taken for a type name, the declared name is swallowed into the
      // specifier list (`typedef unsigned long size_t;` looks like three type specifiers), so it is
      // the last identifier there.
      declarationSpecifiers()?.lastIdentifier()?.let(names::add)
    } else {
      initDeclarators.forEach { it.declarator()?.declaredName()?.let(names::add) }
    }
  }
  for (i in 0 until childCount) getChild(i).collectTypedefNamesInto(names)
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

private fun ParseTree.lastIdentifier(): String? {
  if (this is TerminalNode && symbol.type == CParser.Identifier) return text
  for (i in childCount - 1 downTo 0) {
    getChild(i).lastIdentifier()?.let {
      return it
    }
  }
  return null
}
