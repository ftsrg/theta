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
package hu.bme.mit.theta.xcfa2chc

import hu.bme.mit.theta.common.OsHelper
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.ParamHolder
import hu.bme.mit.theta.core.Relation
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.ParamDecl
import hu.bme.mit.theta.core.plus
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Read
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException
import org.junit.jupiter.api.*
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

private val iParamLut = LinkedHashMap<String, ParamDecl<IntType>>()

private fun iP(name: String) = iParamLut.getOrPut(name) { Decls.Param(name, IntExprs.Int()) }

class TestChcUtils {

  companion object {

    private var solverManager: SmtLibSolverManager? = null
    private val solverFactories: MutableMap<Pair<String, String>, SolverFactory> = LinkedHashMap()

    private val SOLVERS: List<Pair<String, String>> =
      listOf(Pair("z3", "4.12.6"), Pair("z3", "4.13.0"))

    @JvmStatic
    fun solvers(): List<Arguments?> {
      return SOLVERS.map { Arguments.of(it) }
    }

    @BeforeAll
    @JvmStatic
    fun init() {
      if (OsHelper.getOs() == OsHelper.OperatingSystem.LINUX) {
        val home = SmtLibSolverManager.HOME

        solverManager = SmtLibSolverManager.create(home, NullLogger.getInstance())
        for ((solver, version) in SOLVERS) {

          try {
            solverManager!!.install(solver, version, version, null, false)
          } catch (e: SmtLibSolverInstallerException) {
            e.printStackTrace()
          }

          solverFactories.put(
            Pair(solver, version),
            solverManager!!.getSolverFactory(solver, version),
          )
        }
      }
    }

    @AfterAll
    @JvmStatic
    fun destroy() {
      for ((solver, version) in SOLVERS) {
        try {
          solverManager?.uninstall(solver, version)
        } catch (e: SmtLibSolverInstallerException) {
          e.printStackTrace()
        }
      }
    }
  }

  @BeforeEach
  fun before() {
    Assumptions.assumeTrue(OsHelper.getOs() == OsHelper.OperatingSystem.LINUX)
  }

  @ParameterizedTest(name = "[{index}] {0}")
  @MethodSource("solvers")
  fun testPetersonManualCounting(name: Pair<String, String>) {
    val solverFactory = solverFactories[name]!!
    val i2i = ArrayType.of(Int(), Int())

    val pI = ParamHolder(Int())
    val pA = ParamHolder(i2i)
    val br = pA[9]
    val po = pA[10]
    val co = pA[11]
    val rf = pA[12]
    val com = pA[13]
    val prevW = pI[14]
    val eid = pI[15]
    val eid2 = pI[17]
    val vid = pI[18]
    val vid3 = pI[19]
    val eid3 = pI[20]
    val eid4 = pI[21]
    val eid5 = pI[22]
    val eid6 = pI[23]
    val vid4 = pI[24]
    val eid7 = pI[25]
    val eid8 = pI[26]
    val vid5 = pI[27]
    val eid9 = pI[28]
    val eid10 = pI[29]
    val eid11 = pI[50]

    val turn = pI[30]
    val flag1 = pI[31]
    val flag2 = pI[32]
    val cnt = pI[33]
    val turn_old = pI[40]
    val flag1_old = pI[41]
    val flag2_old = pI[42]
    val cnt_old = pI[43]

    val init = Relation("init", i2i, i2i, i2i, i2i, Int()) // br, co, rf, com

    val T0 =
      Relation(
        "T0",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Int(),
        Int(),
        Int(),
        Int(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt
    val T0G =
      Relation(
        "T0_gate",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Int(),
        Int(),
        Int(),
        Int(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt
    val T0C =
      Relation(
        "T0_critical",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Int(),
        Int(),
        Int(),
        Int(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt
    val T0CF =
      Relation(
        "T0_critical_final",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Int(),
        Int(),
        Int(),
        Int(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt
    val T0F =
      Relation(
        "T0_final",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Int(),
        Int(),
        Int(),
        Int(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt

    val T1 =
      Relation(
        "T1",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Int(),
        Int(),
        Int(),
        Int(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt
    val T1G =
      Relation(
        "T1_gate",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Int(),
        Int(),
        Int(),
        Int(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt
    val T1C =
      Relation(
        "T1_critical",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Int(),
        Int(),
        Int(),
        Int(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt
    val T1CF =
      Relation(
        "T1_critical_final",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Int(),
        Int(),
        Int(),
        Int(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt
    val T1F =
      Relation(
        "T1_final",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Int(),
        Int(),
        Int(),
        Int(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt

    val W = Relation("W", i2i, i2i, i2i, i2i, Int(), Int(), Int()) // br, co, rf, com, eid, vid, val

    // problem: unique rf values (W->R) will disable some possible reads

    init(br, co, rf, com, eid) +=
      Eq(eid, Int(0)) + Eq(Read(co, Int(0)), Int(0)) + Eq(Read(com, Int(0)), Int(0))

    W(br, co, rf, com, eid, vid, pI[0]) += // turn := 0
      init(br, co, rf, com, eid).expr + Eq(vid, Int(0)) + Eq(pI[0], Int(0))
    W(br, co, rf, com, eid, vid, pI[0]) += // flag0 := 0
      init(br, co, rf, com, eid).expr + Eq(vid, Int(1)) + Eq(pI[0], Int(0))
    W(br, co, rf, com, eid, vid, pI[0]) += // flag1 := 0
      init(br, co, rf, com, eid).expr + Eq(vid, Int(2)) + Eq(pI[0], Int(0))
    W(br, co, rf, com, eid, vid, pI[0]) += // cnt := 0
      init(br, co, rf, com, eid).expr + Eq(vid, Int(3)) + Eq(pI[0], Int(0))

    T0(br, co, rf, com, eid, turn, flag1, flag2, cnt) +=
      init(br, co, rf, com, eid2).expr + Eq(eid, Int(1))
    T1(br, co, rf, com, eid, turn, flag1, flag2, cnt) +=
      init(br, co, rf, com, eid2).expr + Eq(eid, Int(2))

    W(br, co, rf, com, eid, vid, pI[0]) += // flag0 := 1
      W(br, co, rf, com, eid2, vid, pI[1]).expr + // prevW
        T0(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr +
        Eq(vid, Int(1)) +
        Eq(pI[0], Int(1)) +
        Eq(Add(Read(co, eid2), Int(1)), Read(co, eid)) + // co-next
        Lt(Read(com, eid2), Read(com, eid))
    W(br, co, rf, com, eid, vid, pI[0]) += // flag1 := 1
      W(br, co, rf, com, eid2, vid, pI[1]).expr + // prevW
        T1(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr +
        Eq(vid, Int(2)) +
        Eq(pI[0], Int(1)) +
        Eq(Add(Read(co, eid2), Int(1)), Read(co, eid)) + // co-next
        Lt(Read(com, eid2), Read(com, eid))

    T0G(br, co, rf, com, eid2, turn, flag1, flag2, cnt) +=
      W(br, co, rf, com, eid, vid, pI[0]).expr + // successful write
        T0(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr + // previous loc
        Eq(Add(eid, Int(2)), eid2) + // eid update
        Lt(Read(com, eid), Read(com, eid2)) // com constraint (because po)
    T1G(br, co, rf, com, eid2, turn, flag1, flag2, cnt) +=
      W(br, co, rf, com, eid, vid, pI[0]).expr + // successful write
        T1(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr + // previous loc
        Eq(Add(eid, Int(2)), eid2) + // eid update
        Lt(Read(com, eid), Read(com, eid2)) // com constraint (because po)

    W(br, co, rf, com, eid, vid, pI[0]) += // turn := 0
      W(br, co, rf, com, eid2, vid, pI[1]).expr + // prevW
        T0G(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr +
        Eq(vid, Int(0)) +
        Eq(pI[0], Int(0)) +
        Eq(Add(Read(co, eid2), Int(1)), Read(co, eid)) + // co-next
        Lt(Read(com, eid2), Read(com, eid))
    W(br, co, rf, com, eid, vid, pI[0]) += // turn := 1
      W(br, co, rf, com, eid2, vid, pI[1]).expr + // prevW
        T1G(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr +
        Eq(vid, Int(0)) +
        Eq(pI[0], Int(1)) +
        Eq(Add(Read(co, eid2), Int(1)), Read(co, eid)) + // co-next
        Lt(Read(com, eid2), Read(com, eid))

    T0C(br, co, rf, com, eid2, turn, flag1, flag2, cnt) +=
      W(br, co, rf, com, eid3, vid3, pI[1]).expr + // rf-source
        W(br, co, rf, com, eid4, vid3, pI[2]).expr + // rf-source
        Eq(Add(eid, Int(2)), eid9) + // eid update
        Eq(vid3, Int(2)) + // flag[1] read
        Eq(Read(rf, eid3), eid9) + // rf
        Lt(Read(com, eid3), Read(com, eid9)) + // com constraint (because rf)
        Lt(Read(com, eid9), Read(com, eid4)) + // com constraint (because fr)
        Eq(Add(Read(co, eid3), Int(1)), Read(co, eid4)) + // co-after is eid4
        Eq(pI[1], flag2) +
        W(br, co, rf, com, eid5, vid4, pI[2]).expr + // turn
        W(br, co, rf, com, eid6, vid4, pI[3]).expr + // turn
        Eq(Add(eid, Int(4)), eid10) + // eid update
        Eq(vid4, Int(0)) + // turn read
        Eq(Read(rf, eid10), eid5) + // rf
        Lt(Read(com, eid5), Read(com, eid10)) + // com constraint (because rf)
        Lt(Read(com, eid10), Read(com, eid6)) + // com constraint (because fr)
        Eq(Add(Read(co, eid5), Int(1)), Read(co, eid6)) + // co-after is eid6
        Eq(pI[2], turn) +
        Or(Eq(turn, Int(0)), Eq(flag2, Int(0))) +
        W(br, co, rf, com, eid7, vid5, pI[3]).expr + // turn
        W(br, co, rf, com, eid8, vid5, pI[4]).expr + // turn
        Eq(Add(eid, Int(6)), eid11) + // eid update
        Eq(vid5, Int(3)) + // turn read
        Eq(Read(rf, eid11), eid7) + // rf
        Lt(Read(com, eid7), Read(com, eid11)) + // com constraint (because rf)
        Lt(Read(com, eid11), Read(com, eid8)) + // com constraint (because fr)
        Eq(Add(Read(co, eid7), Int(1)), Read(co, eid8)) + // co-after is eid8
        Eq(pI[3], cnt) +
        W(br, co, rf, com, eid, vid, pI[0]).expr + // successful write
        T0G(br, co, rf, com, eid, turn_old, flag1, flag2_old, cnt_old).expr + // previous loc
        Eq(Add(eid, Int(8)), eid2) + // eid update
        Lt(Read(com, eid), Read(com, eid9)) + // com constraint (because po)
        Lt(Read(com, eid9), Read(com, eid10)) + // com constraint (because po)
        Lt(Read(com, eid10), Read(com, eid11)) + // com constraint (because po)
        Lt(Read(com, eid11), Read(com, eid2)) // com constraint (because po)

    T1C(br, co, rf, com, eid2, turn, flag1, flag2, cnt) +=
      W(br, co, rf, com, eid3, vid3, pI[1]).expr + // rf-source
        W(br, co, rf, com, eid4, vid3, pI[2]).expr + // rf-source
        Eq(Add(eid, Int(2)), eid9) + // eid update
        Eq(vid3, Int(1)) + // flag[0] read
        Eq(Read(rf, eid9), eid3) + // rf
        Lt(Read(com, eid3), Read(com, eid9)) + // com constraint (because rf)
        Lt(Read(com, eid9), Read(com, eid4)) + // com constraint (because fr)
        Eq(Add(Read(co, eid3), Int(1)), Read(co, eid4)) + // co-after is eid4
        Eq(pI[1], flag1) +
        W(br, co, rf, com, eid5, vid4, pI[2]).expr + // turn
        W(br, co, rf, com, eid6, vid4, pI[3]).expr + // turn
        Eq(Add(eid, Int(4)), eid10) + // eid update
        Eq(vid4, Int(0)) + // turn read
        Eq(Read(rf, eid10), eid5) + // rf
        Lt(Read(com, eid5), Read(com, eid10)) + // com constraint (because rf)
        Lt(Read(com, eid10), Read(com, eid6)) + // com constraint (because fr)
        Eq(Add(Read(co, eid5), Int(1)), Read(co, eid6)) + // co-after is eid6
        Eq(pI[2], turn) +
        Or(Eq(turn, Int(1)), Eq(flag1, Int(0))) +
        W(br, co, rf, com, eid7, vid5, pI[3]).expr + // cnt
        W(br, co, rf, com, eid8, vid5, pI[4]).expr + // cnt
        Eq(Add(eid, Int(6)), eid11) + // eid update
        Eq(vid5, Int(3)) + // turn
        Eq(Read(rf, eid11), eid7) + // rf
        Lt(Read(com, eid7), Read(com, eid11)) + // com constraint (because rf)
        Lt(Read(com, eid11), Read(com, eid8)) + // com constraint (because fr)
        Eq(Add(Read(co, eid7), Int(1)), Read(co, eid8)) + // co-after is eid8
        Eq(pI[3], cnt) +
        W(br, co, rf, com, eid, vid, pI[0]).expr + // successful write
        T1G(br, co, rf, com, eid, turn, flag1, flag2, cnt_old).expr + // previous loc
        Eq(Add(eid, Int(8)), eid2) + // eid update
        Lt(Read(com, eid), Read(com, eid9)) + // com constraint (because po)
        Lt(Read(com, eid9), Read(com, eid10)) + // com constraint (because po)
        Lt(Read(com, eid10), Read(com, eid11)) + // com constraint (because po)
        Lt(Read(com, eid11), Read(com, eid2)) // com constraint (because po)

    W(br, co, rf, com, eid, vid, pI[0]) += // cnt := cnt+1
      W(br, co, rf, com, eid2, vid, pI[1]).expr + // prevW
        T0C(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr +
        Eq(vid, Int(3)) +
        Eq(pI[0], Add(cnt, Int(1))) +
        Eq(Add(Read(co, eid2), Int(1)), Read(co, eid)) + // co-next
        Lt(Read(com, eid2), Read(com, eid))
    W(br, co, rf, com, eid, vid, pI[0]) += // cnt := cnt+1
      W(br, co, rf, com, eid2, vid, pI[1]).expr + // prevW
        T1C(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr +
        Eq(vid, Int(3)) +
        Eq(pI[0], Add(cnt, Int(1))) +
        Eq(Add(Read(co, eid2), Int(1)), Read(co, eid)) + // co-next
        Lt(Read(com, eid2), Read(com, eid))

    T0CF(br, co, rf, com, eid2, turn, flag1, flag2, cnt) +=
      W(br, co, rf, com, eid, vid, pI[0]).expr + // successful write
        T0C(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr + // previous loc
        Eq(Add(eid, Int(2)), eid2) + // eid update
        Lt(Read(com, eid), Read(com, eid2)) // com constraint (because po)
    T1CF(br, co, rf, com, eid2, turn, flag1, flag2, cnt) +=
      W(br, co, rf, com, eid, vid, pI[0]).expr + // successful write
        T1C(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr + // previous loc
        Eq(Add(eid, Int(2)), eid2) + // eid update
        Lt(Read(com, eid), Read(com, eid2)) // com constraint (because po)

    W(br, co, rf, com, eid, vid, pI[0]) += // cnt := 0
      W(br, co, rf, com, eid2, vid, pI[1]).expr + // prevW
        T0CF(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr +
        Eq(vid, Int(3)) +
        Eq(pI[0], Int(0)) +
        Eq(Add(Read(co, eid2), Int(1)), Read(co, eid)) + // co-next
        Lt(Read(com, eid2), Read(com, eid))
    W(br, co, rf, com, eid, vid, pI[0]) += // cnt := 0
      W(br, co, rf, com, eid2, vid, pI[1]).expr + // prevW
        T1CF(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr +
        Eq(vid, Int(3)) +
        Eq(pI[0], Int(0)) +
        Eq(Add(Read(co, eid2), Int(1)), Read(co, eid)) + // co-next
        Lt(Read(com, eid2), Read(com, eid))

    T0F(br, co, rf, com, eid2, turn, flag1, flag2, cnt) +=
      W(br, co, rf, com, eid, vid, pI[0]).expr + // successful write
        T0CF(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr + // previous loc
        Eq(Add(eid, Int(2)), eid2) + // eid update
        Lt(Read(com, eid), Read(com, eid2)) // com constraint (because po)
    T1F(br, co, rf, com, eid2, turn, flag1, flag2, cnt) +=
      W(br, co, rf, com, eid, vid, pI[0]).expr + // successful write
        T1CF(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr + // previous loc
        Eq(Add(eid, Int(2)), eid2) + // eid update
        Lt(Read(com, eid), Read(com, eid2)) // com constraint (because po)

    W(br, co, rf, com, eid, vid, pI[0]) += // flag1 := 0
      W(br, co, rf, com, eid2, vid, pI[1]).expr + // prevW
        T0F(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr +
        Eq(vid, Int(1)) +
        Eq(pI[0], Int(0)) +
        Eq(Add(Read(co, eid2), Int(1)), Read(co, eid)) + // co-next
        Lt(Read(com, eid2), Read(com, eid))
    W(br, co, rf, com, eid, vid, pI[0]) += // flag2 := 0
      W(br, co, rf, com, eid2, vid, pI[1]).expr + // prevW
        T1F(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr +
        Eq(vid, Int(2)) +
        Eq(pI[0], Int(0)) +
        Eq(Add(Read(co, eid2), Int(1)), Read(co, eid)) + // co-next
        Lt(Read(com, eid2), Read(com, eid))

    T0(br, co, rf, com, eid2, turn, flag1, flag2, cnt) +=
      W(br, co, rf, com, eid, vid, pI[0]).expr + // successful write
        T0F(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr + // previous loc
        Eq(Add(eid, Int(2)), eid2) + // eid update
        Lt(Read(com, eid), Read(com, eid2)) // com constraint (because po)
    T1(br, co, rf, com, eid, turn, flag1, flag2, cnt) +=
      W(br, co, rf, com, eid, vid, pI[0]).expr + // successful write
        T1F(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr + // previous loc
        Eq(Add(eid, Int(2)), eid2) + // eid update
        Lt(Read(com, eid), Read(com, eid2)) // com constraint (because po)

    !(T0C(br, co, rf, com, eid, turn, flag1, flag2, cnt) with Eq(cnt, Int(1)))
    !(T1C(br, co, rf, com, eid, turn, flag1, flag2, cnt) with Eq(cnt, Int(1)))

    val relations = listOf(init, T0, T0G, T0C, T0CF, T0F, T1, T1G, T1C, T1CF, T1F, W)
    val expr = relations.toSMT2()
    println(expr)
    val solver = solverFactory.createHornSolver()
    solver.add(relations)
    solver.check()
    Assertions.assertTrue(solver.status == SolverStatus.SAT)
  }

  @ParameterizedTest(name = "[{index}] {0}")
  @MethodSource("solvers")
  fun testPetersonNoCounting(name: Pair<String, String>) {
    val solverFactory = solverFactories[name]!!
    val i2i = ArrayType.of(Int(), Int())

    val pI = ParamHolder(Int())
    val pB = ParamHolder(Bool())
    val pA = ParamHolder(i2i)
    val br = pA[9]
    val po = pA[10]
    val co = pA[11]
    val rf = pA[12]
    val com = pA[13]
    val prevW = pI[14]
    val eid = pI[15]
    val eid2 = pI[17]
    val vid = pI[18]
    val vid3 = pI[19]
    val eid3 = pI[20]
    val eid4 = pI[21]
    val eid5 = pI[22]
    val eid6 = pI[23]
    val vid4 = pI[24]
    val eid7 = pI[25]
    val eid8 = pI[26]
    val vid5 = pI[27]
    val eid9 = pI[28]
    val eid10 = pI[29]
    val eid11 = pI[50]

    val turn = pB[30]
    val flag1 = pB[31]
    val flag2 = pB[32]
    val cnt = pB[33]
    val turn_old = pB[40]
    val flag1_old = pB[41]
    val flag2_old = pB[42]

    val init = Relation("init", i2i, i2i, i2i, i2i, Int()) // br, co, rf, com

    val T0 =
      Relation(
        "T0",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Bool(),
        Bool(),
        Bool(),
        Bool(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt
    val T0G =
      Relation(
        "T0_gate",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Bool(),
        Bool(),
        Bool(),
        Bool(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt
    val T0C =
      Relation(
        "T0_critical",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Bool(),
        Bool(),
        Bool(),
        Bool(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt
    val T0F =
      Relation(
        "T0_final",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Bool(),
        Bool(),
        Bool(),
        Bool(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt

    val T1 =
      Relation(
        "T1",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Bool(),
        Bool(),
        Bool(),
        Bool(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt
    val T1G =
      Relation(
        "T1_gate",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Bool(),
        Bool(),
        Bool(),
        Bool(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt
    val T1C =
      Relation(
        "T1_critical",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Bool(),
        Bool(),
        Bool(),
        Bool(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt
    val T1F =
      Relation(
        "T1_final",
        i2i,
        i2i,
        i2i,
        i2i,
        Int(),
        Bool(),
        Bool(),
        Bool(),
        Bool(),
      ) // br, co, rf, com, eid, turn, flag0, flag1, cnt

    val W =
      Relation("W", i2i, i2i, i2i, i2i, Int(), Int(), Bool()) // br, co, rf, com, eid, vid, val

    init(br, co, rf, com, eid) +=
      Eq(eid, Int(0)) + Eq(Read(co, Int(0)), Int(0)) + Eq(Read(com, Int(0)), Int(0))

    W(br, co, rf, com, eid, vid, pB[0]) += // turn := 0
      init(br, co, rf, com, eid).expr + Eq(vid, Int(0)) + Eq(pB[0], False())
    W(br, co, rf, com, eid, vid, pB[0]) += // flag0 := 0
      init(br, co, rf, com, eid).expr + Eq(vid, Int(1)) + Eq(pB[0], False())
    W(br, co, rf, com, eid, vid, pB[0]) += // flag1 := 0
      init(br, co, rf, com, eid).expr + Eq(vid, Int(2)) + Eq(pB[0], False())

    T0(br, co, rf, com, eid, turn, flag1, flag2, cnt) +=
      init(br, co, rf, com, eid2).expr + Eq(eid, Int(1))
    T1(br, co, rf, com, eid, turn, flag1, flag2, cnt) +=
      init(br, co, rf, com, eid2).expr + Eq(eid, Int(2))

    W(br, co, rf, com, eid, vid, pB[0]) += // flag0 := 1
      W(br, co, rf, com, eid2, vid, pB[1]).expr + // prevW
        T0(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr +
        Eq(vid, Int(1)) +
        Eq(pB[0], True()) +
        Eq(Add(Read(co, eid2), Int(1)), Read(co, eid)) + // co-next
        Lt(Read(com, eid2), Read(com, eid))
    W(br, co, rf, com, eid, vid, pB[0]) += // flag1 := 1
      W(br, co, rf, com, eid2, vid, pB[1]).expr + // prevW
        T1(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr +
        Eq(vid, Int(2)) +
        Eq(pB[0], True()) +
        Eq(Add(Read(co, eid2), Int(1)), Read(co, eid)) + // co-next
        Lt(Read(com, eid2), Read(com, eid))

    T0G(br, co, rf, com, eid2, turn, flag1, flag2, cnt) +=
      W(br, co, rf, com, eid, vid, pB[0]).expr + // successful write
        T0(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr + // previous loc
        Eq(Add(eid, Int(2)), eid2) + // eid update
        Lt(Read(com, eid), Read(com, eid2)) // com constraint (because po)
    T1G(br, co, rf, com, eid2, turn, flag1, flag2, cnt) +=
      W(br, co, rf, com, eid, vid, pB[0]).expr + // successful write
        T1(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr + // previous loc
        Eq(Add(eid, Int(2)), eid2) + // eid update
        Lt(Read(com, eid), Read(com, eid2)) // com constraint (because po)

    W(br, co, rf, com, eid, vid, pB[0]) += // turn := 1
      W(br, co, rf, com, eid2, vid, pB[1]).expr + // prevW
        T0G(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr +
        Eq(vid, Int(0)) +
        Eq(pB[0], True()) +
        Eq(Add(Read(co, eid2), Int(1)), Read(co, eid)) + // co-next
        Lt(Read(com, eid2), Read(com, eid))
    W(br, co, rf, com, eid, vid, pB[0]) += // turn := 0
      W(br, co, rf, com, eid2, vid, pB[1]).expr + // prevW
        T1G(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr +
        Eq(vid, Int(0)) +
        Eq(pB[0], False()) +
        Eq(Add(Read(co, eid2), Int(1)), Read(co, eid)) + // co-next
        Lt(Read(com, eid2), Read(com, eid))

    T0C(br, co, rf, com, eid2, turn, flag1, flag2, cnt) +=
      W(br, co, rf, com, eid3, vid3, pB[1]).expr + // rf-source
        W(br, co, rf, com, eid4, vid3, pB[2]).expr + // rf-source
        Eq(Add(eid, Int(2)), eid9) + // eid update
        Eq(vid3, Int(2)) + // flag[1] read
        Eq(Read(rf, eid3), eid9) + // rf
        Lt(Read(com, eid3), Read(com, eid9)) + // com constraint (because rf)
        Lt(Read(com, eid9), Read(com, eid4)) + // com constraint (because fr)
        Eq(Add(Read(co, eid3), Int(1)), Read(co, eid4)) + // co-after is eid4
        Eq(pB[1], flag2) +
        W(br, co, rf, com, eid5, vid4, pB[2]).expr + // turn
        W(br, co, rf, com, eid6, vid4, pB[3]).expr + // turn
        Eq(Add(eid, Int(4)), eid10) + // eid update
        Eq(vid4, Int(0)) + // turn read
        Eq(Read(rf, eid10), eid5) + // rf
        Lt(Read(com, eid5), Read(com, eid10)) + // com constraint (because rf)
        Lt(Read(com, eid10), Read(com, eid6)) + // com constraint (because fr)
        Eq(Add(Read(co, eid5), Int(1)), Read(co, eid6)) + // co-after is eid6
        Eq(pB[2], turn) +
        Or(Not(turn), Not(flag2)) +
        W(br, co, rf, com, eid, vid, pB[0]).expr + // successful write
        T0G(br, co, rf, com, eid, turn_old, flag1, flag2_old, cnt).expr + // previous loc
        Eq(Add(eid, Int(6)), eid2) + // eid update
        Lt(Read(com, eid), Read(com, eid9)) + // com constraint (because po)
        Lt(Read(com, eid9), Read(com, eid10)) + // com constraint (because po)
        Lt(Read(com, eid10), Read(com, eid2)) // com constraint (because po)

    T1C(br, co, rf, com, eid2, turn, flag1, flag2, cnt) +=
      W(br, co, rf, com, eid3, vid3, pB[1]).expr + // rf-source
        W(br, co, rf, com, eid4, vid3, pB[2]).expr + // rf-source
        Eq(Add(eid, Int(2)), eid9) + // eid update
        Eq(vid3, Int(1)) + // flag[0] read
        Eq(Read(rf, eid9), eid3) + // rf
        Lt(Read(com, eid3), Read(com, eid9)) + // com constraint (because rf)
        Lt(Read(com, eid9), Read(com, eid4)) + // com constraint (because fr)
        Eq(Add(Read(co, eid3), Int(1)), Read(co, eid4)) + // co-after is eid4
        Eq(pB[1], flag1) +
        W(br, co, rf, com, eid5, vid4, pB[2]).expr + // turn
        W(br, co, rf, com, eid6, vid4, pB[3]).expr + // turn
        Eq(Add(eid, Int(4)), eid10) + // eid update
        Eq(vid4, Int(0)) + // turn read
        Eq(Read(rf, eid10), eid5) + // rf
        Lt(Read(com, eid5), Read(com, eid10)) + // com constraint (because rf)
        Lt(Read(com, eid10), Read(com, eid6)) + // com constraint (because fr)
        Eq(Add(Read(co, eid5), Int(1)), Read(co, eid6)) + // co-after is eid6
        Eq(pB[2], turn) +
        Or(turn, Not(flag1)) +
        W(br, co, rf, com, eid, vid, pB[0]).expr + // successful write
        T1G(br, co, rf, com, eid, turn_old, flag1_old, flag2, cnt).expr + // previous loc
        Eq(Add(eid, Int(6)), eid2) + // eid update
        Lt(Read(com, eid), Read(com, eid9)) + // com constraint (because po)
        Lt(Read(com, eid9), Read(com, eid10)) + // com constraint (because po)
        Lt(Read(com, eid10), Read(com, eid2)) // com constraint (because po)

    T0F(br, co, rf, com, eid2, turn, flag1, flag2, cnt) +=
      T0C(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr + // previous loc
        Eq(Add(eid, Int(2)), eid2) + // eid update
        Lt(Read(com, eid), Read(com, eid2)) // com constraint (because po)
    T1F(br, co, rf, com, eid2, turn, flag1, flag2, cnt) +=
      T1C(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr + // previous loc
        Eq(Add(eid, Int(2)), eid2) + // eid update
        Lt(Read(com, eid), Read(com, eid2)) // com constraint (because po)

    W(br, co, rf, com, eid, vid, pB[0]) += // cnt := 0
      W(br, co, rf, com, eid2, vid, pB[1]).expr + // prevW
        T0F(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr +
        Eq(vid, Int(1)) +
        Eq(pB[0], False()) +
        Eq(Add(Read(co, eid2), Int(1)), Read(co, eid)) + // co-next
        Lt(Read(com, eid2), Read(com, eid))
    W(br, co, rf, com, eid, vid, pB[0]) += // cnt := 0
      W(br, co, rf, com, eid2, vid, pB[1]).expr + // prevW
        T1F(br, co, rf, com, eid, turn, flag1, flag2, cnt).expr +
        Eq(vid, Int(2)) +
        Eq(pB[0], False()) +
        Eq(Add(Read(co, eid2), Int(1)), Read(co, eid)) + // co-next
        Lt(Read(com, eid2), Read(com, eid))

    !(T0C(br, co, rf, com, eid, turn, flag1, flag2, cnt) with
      T1C(br, co, rf, com, eid2, turn_old, flag1_old, flag2_old, cnt).expr +
        Eq(Read(com, eid), Read(com, eid2)))

    val relations = listOf(init, T0, T0G, T0C, T0F, T1, T1G, T1C, T1F, W)
    val expr = relations.toSMT2()
    println(expr)
    val solver = solverFactory.createHornSolver()
    solver.add(relations)
    solver.check()
    Assertions.assertTrue(solver.status == SolverStatus.SAT)
  }
}
