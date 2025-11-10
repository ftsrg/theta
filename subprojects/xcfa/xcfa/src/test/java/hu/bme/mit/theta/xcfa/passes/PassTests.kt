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
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.bvtype.BvExprs.BvType
import hu.bme.mit.theta.core.type.fptype.FpExprs.FpType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CSignedInt
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CFloat
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
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
    private val property = XcfaProperty(ErrorDetection.ERROR_LOCATION)

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
          passes = listOf(NormalizePass(), DeterministicPass(), ErrorLocationPass(property)),
          input = { (init to final) { "reach_error"() } },
          output = { (init to err) { skip() } },
        ),
        PassTestData(
          global = {},
          passes =
            listOf(
              NormalizePass(),
              DeterministicPass(),
              FinalLocationPass(property),
              UnusedLocRemovalPass(),
            ),
          input = {
            (init to "L1") { "abort"() }
            (init to "L1") { skip() }
            ("L1" to "L2") { "exit"() }
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
            (init to final) { "fabs"("x", "x") }
            (init to final) { "floor"("x", "x") }
            (init to final) { "fmax"("x", "x", "x") }
            (init to final) { "fmin"("x", "x", "x") }
            (init to final) { "sqrt"("x", "x") }
            (init to final) { "round"("x", "x") }
            (init to final) { "trunc"("x", "x") }
            (init to final) { "ceil"("x", "x") }
            (init to final) { "isinf"("y", "x") }
            (init to final) { "isfinite"("y", "x") }
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
            "y" type Int() init "0"
            "ret" type Int() init "0"
            "pid" type Int() init "0"
            "thr1" type Int() init "0"
          },
          passes = listOf(NormalizePass(), DeterministicPass(), CLibraryFunctionsPass()),
          input = {
            (init to "L1") { "pthread_create"("ret", "pid", "0", "thr1", "0") }
            (init to "L2") { "pthread_join"("ret", "pid") }
            (init to "L3") { "pthread_mutex_lock"("0", "x") }
            (init to "L4") { "pthread_mutex_unlock"("0", "x") }
            (init to "L5") { "printf"("ret", "x = %d, y = %d\n", "x", "y") }
            (init to "L6") { "scanf"("ret", "x = %d, y = %d\n", "(ref x Int)", "(ref y Int)") }
          },
          output = {
            (init to "L1") {
              "pid".start("thr1", "0", "0")
              "ret".assign("0")
            }
            (init to "L2") {
              "pid".join()
              "ret".assign("0")
            }
            (init to "L3") { mutex_lock("x") }
            (init to "L4") { mutex_unlock("x") }
            val printfArg1 = "__printf_arg_0_0" type Int()
            val printfArg2 = "__printf_arg_0_1" type Int()
            (init to "L5") {
              printfArg1.assign("x")
              printfArg2.assign("y")
            }
            (init to "L6") {
              havoc("x")
              havoc("y")
            }
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
            (init to "L1") { atomic_begin() }
            (init to "L2") { atomic_end() }
          },
        ),
        PassTestData(
          global = {
            "x" type Int() init "0"
            "y" type Int() init "0"
          },
          passes = listOf(RemoveUnnecessaryAtomicBlocksPass()),
          input = {
            (init to "L1") { atomic_begin() }
            (init to "L2") { atomic_end() }
            (init to "L3") {
              atomic_begin()
              atomic_end()
            }
            (init to "L4") {
              atomic_begin()
              "x".assign("y")
              atomic_end()
              atomic_begin()
              "y".assign("x")
              atomic_end()
            }
            (init to "L5") {
              "x".assign("y")
              atomic_begin()
              nondet {
                havoc("x")
                havoc("y")
              }
              atomic_end()
            }
          },
          output = {
            (init to "L1") { atomic_begin() }
            (init to "L2") { atomic_end() }
            (init to "L3") { skip() }
            (init to "L4") {
              "x".assign("y")
              "y".assign("x")
            }
            (init to "L5") {
              "x".assign("y")
              nondet {
                havoc("x")
                havoc("y")
              }
            }
          },
        ),
        PassTestData(
          global = {
            "x" type Int() init "0"
            "y" type Int() init "0"
          },
          passes = listOf(AtomicReadsOneWritePass(), NormalizePass(), DeterministicPass()),
          input = {
            val a = "a" type Int()
            val b = "b" type Int()
            (init to "L1") {
              a.assign("x")
              b.assign("x")
              "x".assign("y")
              "y".assign("a")
            }
            (init to "L2") {
              "x".assign("y")
              a.assign("x")
            }
          },
          output = {
            val a = "a" type Int()
            val b = "b" type Int()
            val xLocal = "x_l1" type Int()

            (init to "L1") {
              a.assign("x")
              b.assign("x")
              "x".assign("y")
              "y".assign("a")
            }
            (init to "L2") {
              xLocal.assign("x")
              xLocal.assign("y")
              a.assign(xLocal.ref)
              "x".assign(xLocal.ref)
            }
          },
        ),
        PassTestData(
          global = {
            "x" type Int() init "0"
            "y" type Int() init "0"
          },
          passes = listOf(AtomicReadsOneWritePass(), NormalizePass(), DeterministicPass()),
          input = {
            val a = "a" type Int()
            val b = "b" type Int()
            (init to "L3") {
              a.assign("x")
              "y".assign(a.ref)
              "x".assign("y")
              b.assign("x")
            }
          },
          output = {
            val a = "a" type Int()
            val b = "b" type Int()
            val xLocal = "x_l1" type Int()
            val yLocal = "y_l1" type Int()

            (init to "L3") {
              xLocal.assign("x")
              yLocal.assign("y")
              a.assign(xLocal.ref)
              yLocal.assign(a.ref)
              xLocal.assign(yLocal.ref)
              b.assign(xLocal.ref)
              "x".assign(xLocal.ref)
              "y".assign(yLocal.ref)
            }
          },
        ),
        PassTestData(
          global = {
            "x" type Int() init "0"
            "y" type Int() init "0"
          },
          passes = listOf(AtomicReadsOneWritePass(), NormalizePass(), DeterministicPass()),
          input = {
            (init to "L4") {
              atomic_begin()
              "x".assign("y")
            }
            ("L4" to "L5") {
              "y".assign("x")
              atomic_end()
            }
          },
          output = {
            val xLocal = "x_l1" type Int()
            (init to "L4") {
              atomic_begin()
              xLocal.assign("x")
              xLocal.assign("y")
            }
            ("L4" to "L5") {
              "y".assign(xLocal.ref)
              "x".assign(xLocal.ref)
              atomic_end()
            }
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
            listOf(
              NormalizePass(),
              DeterministicPass(),
              UnusedVarPass(NullLogger.getInstance(), property),
            ),
          input = { "tmp" type Int() },
          output = {},
        ),
        PassTestData(
          global = {},
          passes = listOf(NormalizePass(), DeterministicPass(), EliminateSelfLoops()),
          input = { ("L1" to "L1") { assume("1 == 1") } },
          output = null,
        ),
        PassTestData(
          global = {
            global(
              "__arrays_Int_Int_Int_false",
              ArrayType.of(Int(), ArrayType.of(Int(), Int())),
              null,
              true,
            )
          },
          passes = listOf(DereferenceToArrayPass()),
          input = {
            (init to "L1") { "(deref 1 0 Int)" memassign "42" }
            ("L1" to final) { assume("(= (deref 1 0 Int) 42)") }
          },
          output = {
            (init to "L1") {
              "__arrays_Int_Int_Int_false" assign
                "(write __arrays_Int_Int_Int_false 1 (write (read __arrays_Int_Int_Int_false 1) 0 42))"
            }
            ("L1" to final) { assume("(= (read (read __arrays_Int_Int_Int_false 1) 0) 42)") }
          },
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
    val originalGlobalVars = input.parent.getVars().toSet()
    val actualOutput =
      passes.fold(input) { acc, procedurePass -> procedurePass.run(acc) }.build(dummyXcfa)
    if (output != null) {
      val expectedOutput = output.build(dummyXcfa)
      val varLookUp =
        actualOutput.vars
          .mapNotNull { v ->
            expectedOutput.vars.find { it.name == v.name && it.type == v.type }?.let { Pair(v, it) }
          }
          .toMap() +
          (input.parent.getVars() - originalGlobalVars)
            .mapNotNull { v ->
              originalGlobalVars
                .find {
                  it.wrappedVar.name == v.wrappedVar.name && it.wrappedVar.type == v.wrappedVar.type
                }
                ?.let { Pair(v.wrappedVar, it.wrappedVar) }
            }
            .toMap()
      val actualOutputReplacedVars =
        actualOutput.copy(
          params = actualOutput.params.map { it.first.changeVars(varLookUp) to it.second },
          vars = actualOutput.vars.map { it.changeVars(varLookUp) }.toSet(),
          edges = actualOutput.edges.map { it.withLabel(it.label.changeVars(varLookUp)) }.toSet(),
        )
      println("Expecting output:\t$expectedOutput\n   Actual output:\t$actualOutputReplacedVars")
      assertEquals(expectedOutput, actualOutputReplacedVars)
    } else {
      println("   Actual output:\t$actualOutput")
    }
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
    val passes = CPasses(property, parseContext, NullLogger.getInstance())
    val xcfaSource =
      xcfa("example") {
        procedure("main", passes) { (init to final) { "proc1"() } }.start()
        procedure("proc1", passes) { (init to final) { assume("1 == 1") } }
      }

    // Test inline
    assertTrue(
      xcfaSource.procedures
        .first { it.name == "main" }
        .edges
        .none { it.getFlatLabels().any { it is InvokeLabel } }
    )

    // Test inlined procedure removal (not init, not invoked, not started)
    assertTrue(xcfaSource.procedures.none { it.name == "proc1" })
  }

  @Test
  fun testSplit() {
    lateinit var edge: XcfaEdge
    xcfa("example") {
      procedure("main", CPasses(property, parseContext, NullLogger.getInstance())) {
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
