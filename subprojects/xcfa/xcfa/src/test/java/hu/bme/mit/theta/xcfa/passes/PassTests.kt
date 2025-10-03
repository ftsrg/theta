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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.bvtype.BvExprs.BvType
import hu.bme.mit.theta.core.type.fptype.FpExprs.FpType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CSignedInt
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CFloat
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class PassTests {

  class PassTestData(
    global: VarContext.() -> Unit,
    input: XcfaProcedureBuilderContext.() -> Unit,
    output: (XcfaProcedureBuilderContext.() -> Unit)?,
    val passes: List<ProcedurePass>,
  ) : Arguments {

    private val builder = XcfaBuilder("").also { it.global(global) }
    private val inputBuilder = builder.procedure("", input).builder
    private val outputBuilder = output?.let { builder.procedure("", it).builder }

    override fun get(): Array<Any> = Arguments.of(inputBuilder, outputBuilder, passes).get()
  }

  companion object {

    private val dummyXcfa = xcfa("") {}
    private val parseContext = ParseContext()
    private val fpParseContext =
      ParseContext().also { it.arithmetic = ArchitectureConfig.ArithmeticType.bitvector }

    @JvmStatic
    val data: List<Arguments> =
      listOf(
        PassTestData(
          global = {
            "x" type Int() init "0"
            "y" type Int() init "0"
          },
          passes = listOf(NormalizePass(), DeterministicPass()),
          input = {
            (init to final) {
              nondet {
                havoc("x")
                havoc("y")
              }
            }
          },
          output = {
            (init to final) { havoc("x") }
            (init to final) { havoc("y") }
          },
        ),
        PassTestData(
          global = {},
          passes =
            listOf(
              NormalizePass(),
              DeterministicPass(),
              EliminateSelfLoops(),
              LbePass(parseContext, LbePass.LbeLevel.LBE_SEQ),
            ),
          input = {
            (init to "L1") { assume("1 == 1") }
            ("L1" to final) { assume("false") }
          },
          output = {
            (init to final) {
              assume("1 == 1")
              assume("false")
            }
          },
        ),
        PassTestData(
          global = {},
          passes =
            listOf(
              NormalizePass(),
              DeterministicPass(),
              EliminateSelfLoops(),
              LbePass(parseContext, LbePass.LbeLevel.LBE_FULL),
            ),
          input = {
            (init to "L1") { assume("1 == 1") }
            ("L1" to "L2") { assume("1 == 1") }
            ("L2" to final) { assume("false") }
            ("L2" to final) { assume("1 == 2") }
          },
          output = {
            (init to final) {
              assume("1 == 1")
              assume("1 == 1")
              nondet {
                assume("false")
                assume("1 == 2")
              }
            }
          },
        ),
        PassTestData(
          global = {},
          passes = listOf(EmptyEdgeRemovalPass(), UnusedLocRemovalPass()),
          input = {
            (init to "L1") { nop() }
            ("L1" to "L2") { nop() }
            ("L2" to final) { nop() }
          },
          output = {
            (init to "L2") { nop() }
            ("L2" to final) { nop() }
          },
        ),
        PassTestData(
          global = {},
          passes = listOf(NormalizePass(), DeterministicPass(), ErrorLocationPass(false)),
          input = { (init to final) { "reach_error".invoke() } },
          output = { (init to err) { skip() } },
        ),
        PassTestData(
          global = {},
          passes =
            listOf(
              NormalizePass(),
              DeterministicPass(),
              FinalLocationPass(false),
              UnusedLocRemovalPass(),
            ),
          input = {
            (init to "L1") { "abort".invoke() }
            (init to "L1") { skip() }
            ("L1" to "L2") { "exit".invoke() }
          },
          output = {
            (init to final) { assume("false") }
            (init to "L1") { skip() }
            ("L1" to final) { assume("false") }
          },
        ),
        PassTestData(
          global = { "x" type Int() init "0" },
          passes = listOf(LoopUnrollPass()),
          input = {
            (init to "L1") { "x".assign("0") }
            ("L1" to "L2") {
              assume("(< x 3)")
              "x".assign("(+ x 1)")
            }
            ("L2" to "L1") { skip() }
            ("L1" to final) { assume("(= x 3)") }
          },
          output = {
            (init to "L1") { "x".assign("0") }
            ("L1" to "L2_loop0") {
              nop()
              "x".assign("(+ x 1)")
            }
            ("L2_loop0" to "L1_loop0") { skip() }
            ("L1_loop0" to "L2_loop1") {
              nop()
              "x".assign("(+ x 1)")
            }
            ("L2_loop1" to "L1_loop1") { skip() }
            ("L1_loop1" to "L2_loop2") {
              nop()
              "x".assign("(+ x 1)")
            }
            ("L2_loop2" to "L1_loop2") { skip() }
            ("L1_loop2" to final) { nop() }
          },
        ),
        PassTestData(
          global = {
            "y" type BvType(32) init "0"
            ("x" type FpType(8, 24) init "0.0f").also {
              fpParseContext.metadata.create(it.ref, "cType", CFloat(null, fpParseContext))
            }
          },
          passes =
            listOf(NormalizePass(), DeterministicPass(), FpFunctionsToExprsPass(fpParseContext)),
          input = {
            (init to final) { "fabs".invoke("x", "x") }
            (init to final) { "floor".invoke("x", "x") }
            (init to final) { "fmax".invoke("x", "x", "x") }
            (init to final) { "fmin".invoke("x", "x", "x") }
            (init to final) { "sqrt".invoke("x", "x") }
            (init to final) { "round".invoke("x", "x") }
            (init to final) { "trunc".invoke("x", "x") }
            (init to final) { "ceil".invoke("x", "x") }
            (init to final) { "isinf".invoke("y", "x") }
            (init to final) { "isfinite".invoke("y", "x") }
          },
          output = {
            (init to final) { "x".assign("(fpabs x)") }
            (init to final) { "x".assign("(fproundtoint[RTN] x)") }
            (init to final) { "x".assign("(fpmax x x)") }
            (init to final) { "x".assign("(fpmin x x)") }
            (init to final) { "x".assign("(fpsqrt x)") }
            (init to final) { "x".assign("(fproundtoint[RNA] x)") }
            (init to final) { "x".assign("(fproundtoint[RTZ] x)") }
            (init to final) { "x".assign("(fproundtoint[RTP] x)") }
            (init to final) {
              "y"
                .assign(
                  "(ite (isinfinite x) #b00000000000000000000000000000001 #b00000000000000000000000000000000)"
                )
            }
            (init to final) {
              "y"
                .assign(
                  "(ite (or (isinfinite x) (fpisnan x)) #b00000000000000000000000000000000 #b00000000000000000000000000000001)"
                )
            }
          },
        ),
        PassTestData(
          global = {
            "x" type Int() init "0"
            "y" type Int() init "0"
          },
          passes =
            listOf(NormalizePass(), DeterministicPass(), HavocPromotionAndRange(parseContext)),
          input = {
            (init to final) {
              havoc("x")
              "y".assign("x")
            }
          },
          output = { (init to final) { havoc("y") } },
        ),
        PassTestData(
          global = {
            "x" type Int() init "0"
            "y" type Int() init "0"
          },
          passes =
            listOf(NormalizePass(), DeterministicPass(), HavocPromotionAndRange(parseContext)),
          input = {
            (init to final) {
              havoc("x")
              "y".assign("x").also {
                parseContext.metadata.create(
                  ((it.labels.last() as StmtLabel).stmt as AssignStmt<*>).varDecl.ref,
                  "cType",
                  CSignedInt(null, parseContext),
                )
              }
            }
          },
          output = {
            (init to final) {
              havoc("y")
              assume("(and (>= y -2147483648) (<= y 2147483647))")
            }
          },
        ),
        PassTestData(
          global = { "x" type Int() init "0" },
          passes =
            listOf(
              NormalizePass(),
              DeterministicPass(),
              RemoveDeadEnds(parseContext),
              UnusedLocRemovalPass(),
            ),
          input = {
            (init to "L1") { assume("1 == 1") }
            (init to "L2") { assume("1 == 1") }
            ("L2" to "L3") { assume("false") }
            ("L3" to "L2") { assume("false") }
            (init to "L3") { "main"() }
            (init to "L3") { "x".start("main") }
          },
          output = {
            (init to "L3") { "main"() }
            (init to "L3") { "x".start("main") }
          },
        ),
        PassTestData(
          global = {
            "x" type Int() init "0"
            "thr1" type Int() init "0"
          },
          passes = listOf(NormalizePass(), DeterministicPass(), CLibraryFunctionsPass()),
          input = {
            (init to "L1") { "pthread_create"("x", "x", "0", "thr1", "0") }
            (init to "L2") { "pthread_join"("x", "x") }
            (init to "L3") { "pthread_mutex_lock"("0", "x") }
            (init to "L4") { "pthread_mutex_unlock"("0", "x") }
          },
          output = {
            (init to "L1") {
              "x".start("thr1", "0", "0")
              "x".assign("0")
            }
            (init to "L2") {
              "x".join()
              "x".assign("0")
            }
            (init to "L3") { fence("mutex_lock(x)") }
            (init to "L4") { fence("mutex_unlock(x)") }
          },
        ),
        PassTestData(
          global = {},
          passes = listOf(NormalizePass(), DeterministicPass(), SvCompIntrinsicsPass()),
          input = {
            (init to "L1") { "__VERIFIER_atomic_begin"("0") }
            (init to "L2") { "__VERIFIER_atomic_end"("0") }
          },
          output = {
            (init to "L1") { fence("ATOMIC_BEGIN") }
            (init to "L2") { fence("ATOMIC_END") }
          },
        ),
        PassTestData(
          global = {
            "x" type Int() init "0"
            "thr1" type Int() init "0"
          },
          passes = listOf(NormalizePass(), DeterministicPass(), NondetFunctionPass()),
          input = { (init to "L1") { "__VERIFIER_nondet_int"("x") } },
          output = { (init to "L1") { havoc("x") } },
        ),
        PassTestData(
          global = {},
          passes =
            listOf(NormalizePass(), DeterministicPass(), UnusedVarPass(NullLogger.getInstance())),
          input = { "tmp" type Int() },
          output = {},
        ),
        PassTestData(
          global = {},
          passes = listOf(NormalizePass(), DeterministicPass(), EliminateSelfLoops()),
          input = { ("L1" to "L1") { assume("1 == 1") } },
          output = null,
        ),
      )
  }

  @ParameterizedTest
  @MethodSource("getData")
  fun testPass(
    input: XcfaProcedureBuilder,
    output: XcfaProcedureBuilder?,
    passes: List<ProcedurePass>,
  ) {
    println("Trying to run $passes on input...")
    val actualOutput =
      passes.fold(input) { acc, procedurePass -> procedurePass.run(acc) }.build(dummyXcfa)
    if (output != null) {
      val expectedOutput = output.build(dummyXcfa)
      println("Expecting output:\t$expectedOutput\n   Actual output:\t$actualOutput")
      assertEquals(expectedOutput, actualOutput)
    }
    println("   Actual output:\t$actualOutput")
    println("=============PASS=============\n")
  }

  @Test
  fun testChangeVars() {
    val x = Var("x", Int())
    val y = Var("y", Int())
    val xcfaLabel = { a: VarDecl<IntType>, b: VarDecl<IntType> -> StmtLabel(Assign(a, b.ref)) }

    val x_prime = Var("x'", Int())
    assertEquals(xcfaLabel(x, y), xcfaLabel(x, y).changeVars(emptyMap()))
    assertEquals(xcfaLabel(x_prime, y), xcfaLabel(x, y).changeVars(mapOf(Pair(x, x_prime))))
    assertEquals(xcfaLabel(x, x_prime), xcfaLabel(x, y).changeVars(mapOf(Pair(y, x_prime))))
  }

  @Test
  fun testInline() {
    val xcfaSource =
      xcfa("example") {
        procedure(
          "main",
          ProcedurePassManager(
            listOf(NormalizePass(), DeterministicPass(), InlineProceduresPass(parseContext))
          ),
        ) {
          (init to final) { "proc1"() }
        }
        procedure("proc1") { (init to final) { assume("1 == 1") } }
      }

    assertTrue(
      xcfaSource.procedures
        .first { it.name == "main" }
        .edges
        .none { it.getFlatLabels().any { it is InvokeLabel } }
    )
  }

  @Test
  fun testCPipeline() {
    val xcfaSource =
      xcfa("example") {
        procedure("main", CPasses(false, parseContext, NullLogger.getInstance())) {
          (init to final) { "proc1"() }
        }
        procedure("proc1") { (init to final) { assume("1 == 1") } }
      }

    assertTrue(
      xcfaSource.procedures
        .first { it.name == "main" }
        .edges
        .none { it.getFlatLabels().any { it is InvokeLabel } }
    )
  }

  @Test
  fun testSplit() {
    lateinit var edge: XcfaEdge
    val xcfaSource =
      xcfa("example") {
        procedure("main", CPasses(false, parseContext, NullLogger.getInstance())) {
          edge = (init to final) {
            assume("1 == 1")
            "proc1"()
            assume("1 == 1")
          }
        }
      }

    val newEdges = edge.splitIf { it is InvokeLabel }
    assertTrue(newEdges.size == 3)
  }
}
