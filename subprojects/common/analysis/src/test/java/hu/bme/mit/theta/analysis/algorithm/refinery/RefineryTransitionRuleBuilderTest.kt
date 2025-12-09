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
package hu.bme.mit.theta.analysis.algorithm.refinery

import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Symbol
import hu.bme.mit.theta.common.dsl.SymbolTable
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.grammar.dsl.SimpleScope
import hu.bme.mit.theta.grammar.dsl.stmt.StatementWrapper
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class RefineryTransitionRuleBuilderTest {

  companion object {

    private data class NamedSymbol(private val _name: String) : Symbol {

      override fun getName(): String = _name
    }

    private class TestRefineryTransitionRuleBuilder(pointers: Set<Decl<*>>) :
      RefineryTransitionRuleBuilder<Stmt>(variables = mutableSetOf(), pointers = pointers) {
      private var counter = 0

      override fun build(transition: Stmt): Set<RefineryRule> {
        val transitionName = "transition${counter++}"
        val topRootBlock = transition.toRules()
        topRootBlock.setIds()
        return topRootBlock.allRules
          .mapIndexed { index, rule ->
            rule
              .copy(
                preConditionClauses =
                  listOf("loc(env) == \"${transitionName}__${rule.preId}\"") +
                    rule.preConditionClauses,
                actionClauses =
                  rule.actionClauses + listOf("loc(env): \"${transitionName}__${rule.postId}\""),
              )
              .toRefineryRule("${transitionName}__$index")
          }
          .toSet()
      }
    }

    private data class RefineryRuleBuilderTestData(
      val stmt: String,
      val expectedRules: Set<String>,
      val pointers: Set<String> = setOf(),
      val expectedException: Throwable? = null,
    ) : Arguments {

      override fun get(): Array<Any> =
        Arguments.of(stmt, expectedRules, pointers, expectedException).get()
    }

    @JvmStatic
    private fun ruleBuilderData(): Collection<RefineryRuleBuilderTestData> =
      listOf(
        RefineryRuleBuilderTestData(
          "skip",
          setOf(
            """
            |rule transition0__0__0_to_1() <->
            |    loc(env) == "transition0__0"
            |==>
            |    loc(env): "transition0__1".
            """
              .trimMargin()
          ),
        ),
        RefineryRuleBuilderTestData(
          "(assign v 1)",
          setOf(
            """
            |rule transition0__0__0_to_1() <->
            |    loc(env) == "transition0__0"
            |==>
            |    v(env): 1,
            |    loc(env): "transition0__1".
            """
              .trimMargin()
          ),
        ),
        RefineryRuleBuilderTestData(
          "(assign p 0)", // null pointer assignment
          setOf(
            """
            |rule transition0__0__0_to_1(Pointer assigned_pointer, Pointable target) <->
            |    loc(env) == "transition0__0",
            |    name(p) == "p",
            |    pointer(p, assigned_pointer),
            |    target(nullptr, target)
            |==>
            |    target(assigned_pointer, target),
            |    loc(env): "transition0__1".
            """
              .trimMargin()
          ),
          setOf("p"),
        ),
        RefineryRuleBuilderTestData(
          "(assign p 1)",
          setOf(
            """
            |rule transition0__0__0_to_1(Pointer assigned_pointer, MemoryObject base) <->
            |    loc(env) == "transition0__0",
            |    name(p) == "p",
            |    pointer(p, assigned_pointer),
            |    Address(address),
            |    Address::address(address) == 1,
            |    regionExists(region, address),
            |    parts(region, base),
            |    offset(base) == 0
            |==>
            |    target(assigned_pointer, base),
            |    loc(env): "transition0__1".
            """
              .trimMargin(),
            """
            |rule transition0__1__0_to_1(Pointer assigned_pointer, MemoryRegion region, MemoryObject base, Address address) <->
            |    loc(env) == "transition0__0",
            |    name(p) == "p",
            |    pointer(p, assigned_pointer),
            |    Address(address),
            |    Address::address(address) == 1,
            |    !regionExists(region, address)
            |==>
            |    exists(region),
            |    MemoryRegion::address(region, address),
            |    exists(base),
            |    parts(region, base),
            |    offset(base): 0,
            |    target(assigned_pointer, base),
            |    loc(env): "transition0__1".
            """
              .trimMargin(),
          ),
          setOf("p"),
        ),
        RefineryRuleBuilderTestData(
          "(assume (or (and (not (= v1 v2)) true) false))",
          setOf(
            """
            |rule transition0__0__0_to_1() <->
            |    loc(env) == "transition0__0",
            |    ((!(v1(env) == v2(env))) && (true)) || (false)
            |==>
            |    loc(env): "transition0__1".
            """
              .trimMargin()
          ),
        ),
        RefineryRuleBuilderTestData(
          "(assume (not (= (deref p 0 Int) (- 3))))",
          setOf(
            """
            |rule transition0__0__0_to_1() <->
            |    loc(env) == "transition0__0",
            |    name(p) == "p",
            |    pointer(p, pointer_p),
            |    target(pointer_p, base_0),
            |    !(value(base_0) == -(3))
            |==>
            |    loc(env): "transition0__1".
            """
              .trimMargin()
          ),
          setOf("p"),
        ),
        RefineryRuleBuilderTestData(
          "(assign v (deref p 1 Int))",
          setOf(
            """
            |rule transition0__0__0_to_1(Value referenced_0) <->
            |    loc(env) == "transition0__0",
            |    name(p) == "p",
            |    pointer(p, pointer_p),
            |    target(pointer_p, base_0),
            |    parts(region_0, base_0),
            |    parts(region_0, referenced_0),
            |    offset(referenced_0) == offset(base_0) + (1)
            |==>
            |    v(env): value(referenced_0),
            |    loc(env): "transition0__1".
            """
              .trimMargin()
          ),
          setOf("p"),
        ),
        RefineryRuleBuilderTestData(
          "(assign v (deref 1 0 Int))",
          setOf(
            """
            |rule transition0__0__0_to_1(Value base_0) <->
            |    loc(env) == "transition0__0",
            |    Address(address_0),
            |    Address::address(address_0) == 1,
            |    MemoryRegion::address(region_0, address_0),
            |    parts(region_0, base_0),
            |    offset(base_0) == 0
            |==>
            |    v(env): value(base_0),
            |    loc(env): "transition0__1".
            """
              .trimMargin()
          ),
        ),
        RefineryRuleBuilderTestData(
          "(assume (= (deref v 1 Int) p)))",
          setOf(
            """
            |rule transition0__0__0_to_1() <->
            |    loc(env) == "transition0__0",
            |    Address(address_0),
            |    Address::address(address_0) == v(env),
            |    MemoryRegion::address(region_0, address_0),
            |    parts(region_0, base_0),
            |    offset(base_0) == 0,
            |    parts(region_0, base_0),
            |    parts(region_0, referenced_0),
            |    offset(referenced_0) == offset(base_0) + (1),
            |    name(p) == "p",
            |    pointer(p, pointer_p),
            |    target(referenced_0, pointer_comp_target_left_0),
            |    target(pointer_p, pointer_comp_target_right_0),
            |    pointer_comp_target_left_0 == pointer_comp_target_right_0
            |==>
            |    loc(env): "transition0__1".
            """
              .trimMargin()
          ),
          setOf("p"),
          IllegalStateException(
            "Pointer expression expected at (deref v 0 Int), expression v does not yield a pointer expression."
          ),
        ),
        RefineryRuleBuilderTestData(
          "(assume (= (deref (deref p 1 Int) 2 Int) (* 3 4 5)))",
          setOf(
            """
            |rule transition0__0__0_to_1() <->
            |    loc(env) == "transition0__0",
            |    name(p) == "p",
            |    pointer(p, pointer_p),
            |    target(pointer_p, base_0),
            |    parts(region_0, base_0),
            |    parts(region_0, referenced_0),
            |    offset(referenced_0) == offset(base_0) + (1),
            |    target(referenced_0, base_1),
            |    parts(region_1, base_1),
            |    parts(region_1, referenced_1),
            |    offset(referenced_1) == offset(base_1) + (2),
            |    value(referenced_1) == (3) * (4) * (5)
            |==>
            |    loc(env): "transition0__1".
            """
              .trimMargin()
          ),
          setOf("p"),
        ),
        RefineryRuleBuilderTestData(
          "(assume (not (= p q)))",
          setOf(
            """
            |rule transition0__0__0_to_1() <->
            |    loc(env) == "transition0__0",
            |    name(p) == "p",
            |    pointer(p, pointer_p),
            |    name(q) == "q",
            |    pointer(q, pointer_q),
            |    target(pointer_p, pointer_comp_target_left_0),
            |    target(pointer_q, pointer_comp_target_right_0),
            |    !(pointer_comp_target_left_0 == pointer_comp_target_right_0)
            |==>
            |    loc(env): "transition0__1".
            """
              .trimMargin()
          ),
          setOf("p", "q"),
        ),
        RefineryRuleBuilderTestData(
          "(assume (= (deref p 1 Int) (deref q 2 Int)))",
          setOf(
            """
            |rule transition0__0__0_to_1() <->
            |    loc(env) == "transition0__0",
            |    name(p) == "p",
            |    pointer(p, pointer_p),
            |    target(pointer_p, base_0),
            |    parts(region_0, base_0),
            |    parts(region_0, referenced_0),
            |    offset(referenced_0) == offset(base_0) + (1),
            |    name(q) == "q",
            |    pointer(q, pointer_q),
            |    target(pointer_q, base_1),
            |    parts(region_1, base_1),
            |    parts(region_1, referenced_1),
            |    offset(referenced_1) == offset(base_1) + (2),
            |    target(referenced_0, pointer_comp_target_left_0),
            |    target(referenced_1, pointer_comp_target_right_0),
            |    pointer_comp_target_left_0 == pointer_comp_target_right_0
            |==>
            |    loc(env): "transition0__1".
            """
              .trimMargin(),
            """
            |rule transition0__1__0_to_1() <->
            |    loc(env) == "transition0__0",
            |    name(p) == "p",
            |    pointer(p, pointer_p),
            |    target(pointer_p, base_0),
            |    parts(region_0, base_0),
            |    parts(region_0, referenced_0),
            |    offset(referenced_0) == offset(base_0) + (1),
            |    name(q) == "q",
            |    pointer(q, pointer_q),
            |    target(pointer_q, base_1),
            |    parts(region_1, base_1),
            |    parts(region_1, referenced_1),
            |    offset(referenced_1) == offset(base_1) + (2),
            |    value(referenced_0) == value(referenced_1)
            |==>
            |    loc(env): "transition0__1".
            """
              .trimMargin(),
          ),
          setOf("p", "q"),
        ),
        RefineryRuleBuilderTestData(
          "(memassign (deref p 1 Int) (mod v 3))",
          setOf(
            """
            |rule transition0__0__0_to_1(Value referenced_0) <->
            |    loc(env) == "transition0__0",
            |    name(p) == "p",
            |    pointer(p, pointer_p),
            |    target(pointer_p, base_0),
            |    parts(region_0, base_0),
            |    parts(region_0, referenced_0),
            |    offset(referenced_0) == offset(base_0) + (1)
            |==>
            |    value(referenced_0): (v(env)) - (((v(env)) / (3)) * (3)),
            |    loc(env): "transition0__1".
            """
              .trimMargin()
          ),
          setOf("p"),
        ),
        RefineryRuleBuilderTestData(
          "(memassign (deref p 1 Int) q)",
          setOf(
            """
            |rule transition0__0__0_to_1(Pointer referenced_0, Pointable target) <->
            |    loc(env) == "transition0__0",
            |    name(q) == "q",
            |    pointer(q, pointer_q),
            |    name(p) == "p",
            |    pointer(p, pointer_p),
            |    target(pointer_p, base_0),
            |    parts(region_0, base_0),
            |    parts(region_0, referenced_0),
            |    offset(referenced_0) == offset(base_0) + (1),
            |    target(pointer_q, target)
            |==>
            |    target(referenced_0, target),
            |    loc(env): "transition0__1".
            """
              .trimMargin()
          ),
          setOf("p", "q"),
        ),
        RefineryRuleBuilderTestData(
          "(memassign (deref p 1 Int) (deref p 2 Int))",
          setOf(
            """
            |rule transition0__0__0_to_1(Pointer referenced_1, Pointable target) <->
            |    loc(env) == "transition0__0",
            |    name(p) == "p",
            |    pointer(p, pointer_p),
            |    target(pointer_p, base_0),
            |    parts(region_0, base_0),
            |    parts(region_0, referenced_0),
            |    offset(referenced_0) == offset(base_0) + (2),
            |    name(p) == "p",
            |    pointer(p, pointer_p),
            |    target(pointer_p, base_1),
            |    parts(region_1, base_1),
            |    parts(region_1, referenced_1),
            |    offset(referenced_1) == offset(base_1) + (1),
            |    target(referenced_0, target)
            |==>
            |    target(referenced_1, target),
            |    loc(env): "transition0__1".
            """
              .trimMargin(),
            """
            |rule transition0__1__0_to_1(Value referenced_1, Value referenced_0) <->
            |    loc(env) == "transition0__0",
            |    name(p) == "p",
            |    pointer(p, pointer_p),
            |    target(pointer_p, base_0),
            |    parts(region_0, base_0),
            |    parts(region_0, referenced_0),
            |    offset(referenced_0) == offset(base_0) + (2),
            |    name(p) == "p",
            |    pointer(p, pointer_p),
            |    target(pointer_p, base_1),
            |    parts(region_1, base_1),
            |    parts(region_1, referenced_1),
            |    offset(referenced_1) == offset(base_1) + (1)
            |==>
            |    value(referenced_1): value(referenced_0),
            |    loc(env): "transition0__1".
            """
              .trimMargin(),
          ),
          setOf("p"),
        ),
        RefineryRuleBuilderTestData(
          "(assign q (ite (/= p 0) p 0))",
          setOf(
            """
            |rule transition0__0__0_to_1(Pointer assigned_pointer, Pointable target) <->
            |    loc(env) == "transition0__0",
            |    name(q) == "q",
            |    pointer(q, assigned_pointer),
            |    name(p) == "p",
            |    pointer(p, pointer_p),
            |    target(pointer_p, pointer_comp_target_left_0),
            |    target(nullptr, pointer_comp_target_right_0),
            |    pointer_comp_target_left_0 != pointer_comp_target_right_0,
            |    name(p) == "p",
            |    pointer(p, pointer_p),
            |    target(pointer_p, target)
            |==>
            |    target(assigned_pointer, target),
            |    loc(env): "transition0__1".
            """
              .trimMargin(),
            """
            |rule transition0__1__0_to_1(Pointer assigned_pointer, Pointable target) <->
            |    loc(env) == "transition0__0",
            |    name(q) == "q",
            |    pointer(q, assigned_pointer),
            |    name(p) == "p",
            |    pointer(p, pointer_p),
            |    target(pointer_p, pointer_comp_target_left_0),
            |    target(nullptr, pointer_comp_target_right_0),
            |    !(pointer_comp_target_left_0 != pointer_comp_target_right_0),
            |    target(nullptr, target)
            |==>
            |    target(assigned_pointer, target),
            |    loc(env): "transition0__1".
            """
              .trimMargin(),
          ),
          setOf("p", "q"),
        ),
        RefineryRuleBuilderTestData(
          "(assume (= (+ p q) 0))",
          setOf(),
          setOf("p", "q"),
          IllegalStateException("At least one expression expected at (+ p q), but got none."),
        ),
      )

    private val symbols =
      listOf(
        NamedSymbol("v") to Decls.Var("v", Int()),
        NamedSymbol("v1") to Decls.Var("v1", Int()),
        NamedSymbol("v2") to Decls.Var("v2", Int()),
        NamedSymbol("p") to Decls.Var("p", Int()),
        NamedSymbol("q") to Decls.Var("q", Int()),
      )
  }

  @ParameterizedTest
  @MethodSource("ruleBuilderData")
  fun testRefineryRuleBuilder(
    stmtStr: String,
    expectedRules: Set<String>,
    pointers: Set<String>,
    expectedException: Throwable?,
  ) {
    println("Testing statement: $stmtStr with pointers: $pointers")
    val symbolTable = SymbolTable()
    val env = Env()
    for ((symbol, decl) in symbols) {
      symbolTable.add(symbol)
      env.define(symbol, decl)
    }
    val scope = SimpleScope(symbolTable)

    val stmt = StatementWrapper(stmtStr, scope).instantiate(env)

    val vars = StmtUtils.getVars(stmt)
    val pointerDecls = pointers.map { p -> vars.first { it.name == p } }.toSet()
    val builder = TestRefineryTransitionRuleBuilder(pointerDecls)

    val rules =
      try {
        builder.build(stmt)
      } catch (e: Throwable) {
        if (expectedException != null) {
          assertEquals(expectedException::class, e::class)
          assertEquals(expectedException.message, e.message)
          return
        }
        throw e
      }

    assertEquals(
      expectedRules.map { it.trim() }.toSet(),
      rules.map { it.toString().trim() }.toSet(),
    )
  }

  @Test
  fun testRefineryRuleBuilderIds() {
    val ruleBlockIdTester =
      object : RefineryTransitionRuleBuilder<Any>(mutableSetOf(), setOf()) {

        fun test() {
          tests.forEach { t ->
            t.setIds()

            val allIds = t.allRules.flatMap { listOf(it.preId, it.postId) }.toSet()
            for (id1 in allIds) {
              for (id2 in allIds) {
                if (id1 !== id2) {
                  assertTrue(id1.id != id2.id) { "Duplicate id found: $id1 in test $t" }
                }
              }
            }

            t.allNondetBlocks.forEach { nondetBlock ->
              val branchStartIds = nondetBlock.branches.map { it.preId }
              val branchEndIds = nondetBlock.branches.map { it.postId }
              for (id1 in branchStartIds) {
                for (id2 in branchStartIds) {
                  assertTrue(id1 == id2) {
                    "Nondet rule branch start ids do not match: $id1 and $id2 in test $t"
                  }
                }
              }
              for (id1 in branchEndIds) {
                for (id2 in branchEndIds) {
                  assertTrue(id1 == id2) {
                    "Nondet rule branch end ids do not match: $id1 and $id2 in test $t"
                  }
                }
              }
            }
          }
        }

        val tests: Collection<RefineryRuleBlock> =
          listOf(
            simple(),
            sequence(simple(), simple(), simple()),
            nondet(simple(), simple(), simple()),
            sequence(simple(), nondet(simple(), simple()), simple()),
            nondet(simple(), simple(), sequence(simple(), simple())),
            sequence(simple(), sequence(simple(), simple())),
            nondet(simple(), nondet(simple()), nondet(simple(), simple())),
            sequence(
              nondet(simple(), simple()),
              simple(),
              nondet(simple(), sequence(simple(), nondet(simple(), simple())), simple()),
            ),
          )

        private fun simple() =
          SingleRefineryRule(preConditionClauses = listOf(), actionClauses = listOf())

        private fun sequence(vararg blocks: RefineryRuleBlock) =
          SequenceRefineryRuleBlock(blocks.toList())

        private fun nondet(vararg blocks: RefineryRuleBlock) =
          NondetRefineryRuleBlock(blocks.toSet())

        private val RefineryRuleBlock.allNondetBlocks: Set<NondetRefineryRuleBlock>
          get() =
            when (this) {
              is NondetRefineryRuleBlock -> setOf(this) + branches.flatMap { it.allNondetBlocks }
              is SequenceRefineryRuleBlock -> blocks.flatMap { it.allNondetBlocks }.toSet()
              is SingleRefineryRule -> emptySet()
            }

        override fun build(transition: Any): Set<RefineryRule> = error("Not needed")
      }

    ruleBlockIdTester.test()
  }
}
