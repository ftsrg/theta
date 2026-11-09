/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.cli.utils

import com.charleskorn.kaml.Yaml
import com.charleskorn.kaml.YamlList
import com.charleskorn.kaml.YamlMap
import com.charleskorn.kaml.YamlNode
import com.charleskorn.kaml.YamlScalar
import hu.bme.mit.theta.c.frontend.dsl.gen.CLexer
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.ParserRuleContext
import org.antlr.v4.runtime.misc.Interval

/**
 * The API a client may use, as read from the `--library` description:
 * ```
 * max_buffer: 16            # optional bound on client buffers, in elements (default: any size)
 * classes:
 *   - struct: C             # struct tag of the class in the C input
 *     constructors: [C__C]
 *     destructor: C___C     # optional
 *     methods: [C__f, C__g]
 * functions: [h]            # free functions
 * initializers: [init]      # optional: called once first, like the static initializers
 * max_actions: 4            # optional bound on the number of calls (bug finding by BMC)
 * nondet_contents: false   # optional: buffers keep the initial memory (fewer clients: bug finding)
 * ```
 */
data class LibraryApi(
  val classes: List<LibraryClass>,
  val functions: List<String>,
  val maxBuffer: Long?,
  val initializers: List<String> = emptyList(),
  val maxActions: Long? = null,
  val nondetContents: Boolean = true,
) {
  companion object {
    fun parse(text: String): LibraryApi {
      val root = Yaml.default.parseToYamlNode(text) as YamlMap
      fun YamlNode?.strings() =
        (this as? YamlList)?.items?.map { (it as YamlScalar).content } ?: emptyList()
      val classes =
        (root.get<YamlNode>("classes") as? YamlList)?.items?.map {
          val c = it as YamlMap
          LibraryClass(
            struct = c.get<YamlScalar>("struct")!!.content,
            constructors = c.get<YamlNode>("constructors").strings(),
            destructor = c.get<YamlScalar>("destructor")?.content,
            methods = c.get<YamlNode>("methods").strings(),
          )
        } ?: emptyList()
      val maxBuffer = root.get<YamlScalar>("max_buffer")?.content?.toLong()?.takeIf { it > 0 }
      return LibraryApi(
        classes,
        root.get<YamlNode>("functions").strings(),
        maxBuffer,
        root.get<YamlNode>("initializers").strings(),
        root.get<YamlScalar>("max_actions")?.content?.toLong()?.takeIf { it > 0 },
        root.get<YamlScalar>("nondet_contents")?.content?.toBooleanStrict() ?: true,
      )
    }
  }
}

data class LibraryClass(
  val struct: String,
  val constructors: List<String>,
  val destructor: String?,
  val methods: List<String>,
)

/**
 * Builds the most general client of a library: an endless loop that, in each round, makes one call
 * a client could make. An object of an API class is constructed before its methods are called and
 * is not used after its destructor; a pointer argument is a fresh client buffer of any size and
 * contents (or a live API object, for a pointer to an API class); an integer argument right after a
 * buffer is taken to be its length and is at most the buffer's size. A client may catch whatever a
 * call throws. The loop never exits, so what the client allocates and never frees is no error.
 */
class LibraryClient(
  private val program: String,
  private val api: LibraryApi,
  /** Whether fresh memory reads 0, so that a client buffer has to be filled to be arbitrary. */
  private val zeroMemory: Boolean = true,
) {

  private data class Param(val type: String, val isFunctionPointer: Boolean)

  private data class Signature(val name: String, val params: List<Param>)

  private val signatures = HashMap<String, Signature>()
  private val mainTokens = ArrayList<Interval>()
  private val apiStructs = api.classes.map { it.struct }.toSet()

  init {
    val stream = CharStreams.fromString(program)
    val tokens = CommonTokenStream(CLexer(stream))
    val unit = CParser(tokens).compilationUnit()
    unit.translationUnit()?.externalDeclaration()?.forEach { decl ->
      if (decl is CParser.ExternalFunctionDefinitionContext) {
        signature(decl.functionDefinition().declarator(), stream)?.let { signatures[it.name] = it }
      }
    }
    tokens.tokens
      .filter { it.type == CLexer.Identifier && it.text == "main" }
      .forEach { mainTokens.add(Interval.of(it.startIndex, it.stopIndex)) }
  }

  private fun text(ctx: ParserRuleContext, stream: org.antlr.v4.runtime.CharStream) =
    stream.getText(Interval.of(ctx.start.startIndex, ctx.stop.stopIndex))

  private fun signature(
    declarator: CParser.DeclaratorContext,
    stream: org.antlr.v4.runtime.CharStream,
  ): Signature? {
    var direct = declarator.directDeclarator()
    while (direct is CParser.DirectDeclaratorBracesContext) {
      direct = direct.declarator().directDeclarator()
    }
    val function = direct as? CParser.DirectDeclaratorFunctionDeclContext ?: return null
    val name =
      (function.directDeclarator() as? CParser.DirectDeclaratorIdContext)?.text ?: return null
    val params =
      function.parameterTypeList()?.parameterList()?.parameterDeclaration()?.mapNotNull { p ->
        when (p) {
          is CParser.OrdinaryParameterDeclarationContext -> {
            val d = p.declarator()
            val stars = d.pointer()?.let { text(it, stream) } ?: ""
            Param(
              normalize(text(p.declarationSpecifiers(), stream) + " " + stars),
              d.directDeclarator() !is CParser.DirectDeclaratorIdContext,
            )
          }
          is CParser.AbstractParameterDeclarationContext -> {
            val t = normalize(text(p, stream))
            if (t == "void") null else Param(t, t.contains("("))
          }
          else -> null
        }
      } ?: emptyList()
    return Signature(name, params)
  }

  private fun normalize(type: String) =
    type
      .replace(Regex("\\bconst\\b|\\bvolatile\\b|\\brestrict\\b|__attribute__\\(\\(.*?\\)\\)"), " ")
      .replace("*", " * ")
      .trim()
      .split(Regex("\\s+"))
      .joinToString(" ")
      .replace(" *", "*")

  private fun signatureOf(name: String) =
    signatures[name] ?: error("Library API function $name has no definition in the input")

  private val nondets =
    mapOf(
      "_Bool" to "__VERIFIER_nondet_bool",
      "char" to "__VERIFIER_nondet_char",
      "signed char" to "__VERIFIER_nondet_char",
      "unsigned char" to "__VERIFIER_nondet_uchar",
      "short" to "__VERIFIER_nondet_short",
      "unsigned short" to "__VERIFIER_nondet_ushort",
      "int" to "__VERIFIER_nondet_int",
      "unsigned int" to "__VERIFIER_nondet_uint",
      "long" to "__VERIFIER_nondet_long",
      "unsigned long" to "__VERIFIER_nondet_ulong",
      "long long" to "__VERIFIER_nondet_longlong",
      "unsigned long long" to "__VERIFIER_nondet_ulonglong",
      "float" to "__VERIFIER_nondet_float",
      "double" to "__VERIFIER_nondet_double",
    )

  private val unsignedTypes = nondets.keys.filter { it.startsWith("unsigned") || it == "_Bool" }

  private class Call(val guard: List<String>, val body: List<String>)

  /** The statements making the arguments of [sig] and the call itself; `receiver` binds param 0. */
  private fun call(sig: Signature, receiver: String?, site: String): Call {
    val guard = ArrayList<String>()
    val body = ArrayList<String>()
    val args = ArrayList<String>()
    var lastBuffer: String? = null
    sig.params.forEachIndexed { k, p ->
      val a = "${site}_a$k"
      val t = p.type
      var buffer: String? = null
      when {
        k == 0 && receiver != null -> args.add(receiver)
        p.isFunctionPointer -> args.add("0")
        t in nondets && lastBuffer != null && t != "_Bool" && api.maxBuffer != null ->
          // A length within a bounded buffer: counted up, so every value is concrete (see below).
          body
            .add("$t $a = 0; while ((unsigned long) $a < $lastBuffer && $NONDET_BOOL()) $a++;")
            .also { args.add(a) }
        t in nondets -> {
          body.add("$t $a = ${nondets[t]}();")
          if (lastBuffer != null && t != "_Bool") {
            val nonNegative = if (t in unsignedTypes) "" else "$a >= 0 && "
            body.add("if (!($nonNegative(unsigned long) $a <= $lastBuffer)) abort();")
          }
          args.add(a)
        }
        t.endsWith("*") -> {
          val base = t.dropLast(1).trim()
          val struct = base.removePrefix("struct ").takeIf { base.startsWith("struct ") }
          if (struct != null && struct in apiStructs) {
            guard.add("__theta_live_$struct")
            args.add("&__theta_obj_$struct")
          } else {
            val element = if (base == "void") "char" else base
            val count = "${a}_n"
            if (struct != null) {
              body.add("unsigned long $count = 1;")
            } else {
              // A bounded size is counted up from 0 rather than havocked and then restricted, so
              // that explicit-value analyses see each size as a value instead of an unknown.
              val max = api.maxBuffer
              if (max != null) {
                body.add(
                  "unsigned long $count = 0; while ($count < ${max}UL && $NONDET_BOOL()) $count++;"
                )
              } else {
                body.add("unsigned long $count = __VERIFIER_nondet_ulong();")
              }
              buffer = count
            }
            body.add("$element* $a = malloc($count * sizeof($element));")
            body.add("if (!$a) abort();")
            // A pointer slot is cleared either way: the library is not handed a dangling pointer.
            val fill = if (element.endsWith("*")) "0" else "__VERIFIER_nondet_uchar()"
            if ((zeroMemory && api.nondetContents) || element.endsWith("*")) {
              body.add(
                "for (unsigned long ${a}_i = 0; ${a}_i < $count * sizeof($element); ${a}_i++)" +
                  " ((unsigned char*) $a)[${a}_i] = $fill;"
              )
            }
            args.add(a)
          }
        }
        else -> {
          body.add("$t $a;")
          body.add(
            "for (unsigned long ${a}_i = 0; ${a}_i < sizeof($t); ${a}_i++)" +
              " ((unsigned char*) &$a)[${a}_i] = __VERIFIER_nondet_uchar();"
          )
          args.add(a)
        }
      }
      lastBuffer = buffer
    }
    body.add("${sig.name}(${args.joinToString(", ")});")
    if (catchesExceptions) body.add(CATCH)
    return Call(guard, body)
  }

  private val catchesExceptions = program.contains("static int __cir_exc_active;")

  /** The input with any `main` renamed away, followed by the most general client as `main`. */
  fun source(): String {
    val program = StringBuilder(this.program)
    mainTokens.reversed().forEach { program.replace(it.a, it.b + 1, "__theta_library_input_main") }
    val actions = ArrayList<Pair<Call, List<String>>>()
    for (c in api.classes) {
      val live = "__theta_live_${c.struct}"
      val obj = "&__theta_obj_${c.struct}"
      c.constructors.forEachIndexed { i, f ->
        val call = call(signatureOf(f), obj, "__theta_c${actions.size}")
        val construct = if (catchesExceptions) "if (!__theta_threw) $live = 1;" else "$live = 1;"
        actions.add(Call(listOf("!$live") + call.guard, call.body) to listOf(construct))
      }
      for (f in c.methods) {
        val call = call(signatureOf(f), obj, "__theta_c${actions.size}")
        actions.add(Call(listOf(live) + call.guard, call.body) to emptyList())
      }
      c.destructor?.let {
        val call = call(signatureOf(it), obj, "__theta_c${actions.size}")
        actions.add(Call(listOf(live) + call.guard, call.body) to listOf("$live = 0;"))
      }
    }
    for (f in api.functions) {
      actions.add(call(signatureOf(f), null, "__theta_c${actions.size}") to emptyList())
    }
    check(actions.isNotEmpty()) { "The library API description lists no function" }

    val out = StringBuilder()
    out.append("\n// Most general client of the library, generated by Theta (--library).\n")
    out.append("extern void abort(void);\nextern void *malloc(unsigned long);\n")
    nondets.entries
      .distinctBy { it.value }
      .forEach { (t, f) -> out.append("extern $t $f(void);\n") }
    out.append("int main(void) {\n")
    for (c in api.classes) {
      out.append("  struct ${c.struct} __theta_obj_${c.struct};\n")
      out.append("  int __theta_live_${c.struct} = 0;\n")
    }
    for (f in api.initializers) {
      out.append("  ${signatureOf(f).name}();\n")
      if (catchesExceptions) out.append("  if (__cir_exc_active) abort();\n")
    }
    val loop = api.maxActions?.let { "for (long __theta_k = 0; __theta_k < ${it}L; __theta_k++)" }
    out.append("  ${loop ?: "while (1)"} {\n")
    out.append("    int __theta_action = __VERIFIER_nondet_int();\n")
    if (catchesExceptions) out.append("    int __theta_threw = 0;\n")
    actions.forEachIndexed { i, (call, after) ->
      val guard = (listOf("__theta_action == $i") + call.guard).joinToString(" && ")
      out.append("    ${if (i == 0) "if" else "} else if"} ($guard) {\n")
      (call.body + after).forEach { out.append("      $it\n") }
    }
    out.append("    }\n  }\n")
    // The client never exits, so the blocks it still holds are not reported as leaks.
    if (loop != null) out.append("  while (1) {}\n")
    out.append("  return 0;\n}\n")
    return program.append(out).toString()
  }

  companion object {
    private const val NONDET_BOOL = "__VERIFIER_nondet_bool"

    /** A client may catch anything: cir2c's model of a catch-all clause. */
    private const val CATCH =
      "if (__cir_exc_active) { __cir_exc_active = 0; __theta_threw = 1;" +
        " if (__cir_exc_dtor) { void (*__d)(void*) = (void (*)(void*)) __cir_exc_dtor;" +
        " __d(__cir_exc_ptr); __cir_exc_dtor = (void*) 0; } }"
  }
}
