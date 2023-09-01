/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.graphsolver

import hu.bme.mit.theta.common.Tuple
import hu.bme.mit.theta.common.Tuple1
import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.graphsolver.compilers.GraphPatternCompiler
import hu.bme.mit.theta.graphsolver.compilers.pattern2expr.Pattern2ExprCompiler
import hu.bme.mit.theta.graphsolver.patterns.constraints.*
import hu.bme.mit.theta.graphsolver.patterns.patterns.*
import hu.bme.mit.theta.graphsolver.solvers.GraphSolver
import hu.bme.mit.theta.graphsolver.solvers.SATGraphSolver
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import org.junit.runners.Parameterized
import java.util.*

class GraphSolverTest<T> {

    @ParameterizedTest
    @MethodSource("data")
    fun test(
        constraint: GraphConstraint,
        compiler: GraphPatternCompiler<T, *>,
        graphEvents: List<Int>,
        graphEdges: Map<Pair<String, Tuple>, ThreeVL>,
        solver: GraphSolver<T>,
        allowed: Boolean,
    ) {
        compiler.addEvents(graphEvents)
        compiler.addFacts(graphEdges)
        val compiledConstraint = constraint.accept(compiler)
        solver.add(compiledConstraint)
        val status = solver.check()
        Assertions.assertEquals(allowed, status.isSat)
    }

    companion object {

        private val smallLine: Pair<List<Int>, Map<Pair<String, Tuple>, ThreeVL>> = Pair(listOf(1, 2, 3), mapOf(
            Pair(Pair("po", Tuple2.of(1, 1)), ThreeVL.FALSE),
            Pair(Pair("po", Tuple2.of(1, 2)), ThreeVL.TRUE),
            Pair(Pair("po", Tuple2.of(1, 3)), ThreeVL.FALSE),
            Pair(Pair("po", Tuple2.of(2, 1)), ThreeVL.FALSE),
            Pair(Pair("po", Tuple2.of(2, 2)), ThreeVL.FALSE),
            Pair(Pair("po", Tuple2.of(2, 3)), ThreeVL.TRUE),
            Pair(Pair("po", Tuple2.of(3, 1)), ThreeVL.FALSE),
            Pair(Pair("po", Tuple2.of(3, 2)), ThreeVL.FALSE),
            Pair(Pair("po", Tuple2.of(3, 3)), ThreeVL.FALSE),
        ))

        private val smallCycle: Pair<List<Int>, Map<Pair<String, Tuple>, ThreeVL>> = Pair(listOf(1, 2, 3), mapOf(
            Pair(Pair("po", Tuple2.of(1, 1)), ThreeVL.FALSE),
            Pair(Pair("po", Tuple2.of(1, 2)), ThreeVL.TRUE),
            Pair(Pair("po", Tuple2.of(1, 3)), ThreeVL.FALSE),
            Pair(Pair("po", Tuple2.of(2, 1)), ThreeVL.FALSE),
            Pair(Pair("po", Tuple2.of(2, 2)), ThreeVL.FALSE),
            Pair(Pair("po", Tuple2.of(2, 3)), ThreeVL.TRUE),
            Pair(Pair("po", Tuple2.of(3, 1)), ThreeVL.TRUE),
            Pair(Pair("po", Tuple2.of(3, 2)), ThreeVL.FALSE),
            Pair(Pair("po", Tuple2.of(3, 3)), ThreeVL.FALSE),
        ))

        private val smallFull: Pair<List<Int>, Map<Pair<String, Tuple>, ThreeVL>> = Pair(listOf(1, 2, 3), mapOf(
            Pair(Pair("po", Tuple2.of(1, 1)), ThreeVL.TRUE),
            Pair(Pair("po", Tuple2.of(1, 2)), ThreeVL.TRUE),
            Pair(Pair("po", Tuple2.of(1, 3)), ThreeVL.TRUE),
            Pair(Pair("po", Tuple2.of(2, 1)), ThreeVL.TRUE),
            Pair(Pair("po", Tuple2.of(2, 2)), ThreeVL.TRUE),
            Pair(Pair("po", Tuple2.of(2, 3)), ThreeVL.TRUE),
            Pair(Pair("po", Tuple2.of(3, 1)), ThreeVL.TRUE),
            Pair(Pair("po", Tuple2.of(3, 2)), ThreeVL.TRUE),
            Pair(Pair("po", Tuple2.of(3, 3)), ThreeVL.TRUE),
            Pair(Pair("W", Tuple1.of(1)), ThreeVL.TRUE),
            Pair(Pair("R", Tuple1.of(2)), ThreeVL.TRUE),
            Pair(Pair("F", Tuple1.of(3)), ThreeVL.TRUE),
        ))

        @Parameterized.Parameters
        @JvmStatic
        fun data(): Collection<Array<Any>> {
            return Arrays.asList(
                arrayOf(
                    Acyclic(BasicRelation("po")),
                    Pattern2ExprCompiler(),
                    smallLine.first,
                    smallLine.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Acyclic(BasicRelation("po")),
                    Pattern2ExprCompiler(),
                    smallCycle.first,
                    smallCycle.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    false
                ),
                arrayOf(
                    Acyclic(BasicRelation("po")),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    false
                ),
                arrayOf(
                    Cyclic(BasicRelation("po")),
                    Pattern2ExprCompiler(),
                    smallLine.first,
                    smallLine.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    false
                ),
                arrayOf(
                    Cyclic(BasicRelation("po")),
                    Pattern2ExprCompiler(),
                    smallCycle.first,
                    smallCycle.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Cyclic(BasicRelation("po")),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Reflexive(BasicRelation("po")),
                    Pattern2ExprCompiler(),
                    smallLine.first,
                    smallLine.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    false
                ),
                arrayOf(
                    Reflexive(BasicRelation("po")),
                    Pattern2ExprCompiler(),
                    smallCycle.first,
                    smallCycle.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    false
                ),
                arrayOf(
                    Reflexive(BasicRelation("po")),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Irreflexive(BasicRelation("po")),
                    Pattern2ExprCompiler(),
                    smallLine.first,
                    smallLine.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Irreflexive(BasicRelation("po")),
                    Pattern2ExprCompiler(),
                    smallCycle.first,
                    smallCycle.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Irreflexive(BasicRelation("po")),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    false
                ),
                arrayOf(
                    Irreflexive(CartesianProduct(BasicEventSet("W"), BasicEventSet("R"))),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Irreflexive(IdentityClosure(BasicRelation("rf"))),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    false
                ),
                arrayOf(
                    Empty(Difference(BasicRelation("po"), BasicRelation("po"))),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Empty(DifferenceNode(Domain(BasicRelation("po")), Range(BasicRelation("po")))),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Empty(Complement(BasicRelation("po"))),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Empty(ComplementNode(Domain(BasicRelation("po")))),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Empty(EmptyRel),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Empty(EmptySet),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Empty(Intersection(EmptyRel, BasicRelation("po"))),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Empty(IntersectionNode(EmptySet, BasicEventSet("W"))),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Empty(Complement(Union(Self(BasicRelation("po")), BasicRelation("po")))),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Nonempty(Union(ReflexiveTransitiveClosure(BasicRelation("po")), BasicRelation("po"))),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Empty(UnionNode(BasicEventSet("W"), BasicEventSet("R"))),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Empty(Difference(Inverse(BasicRelation("po")), BasicRelation("po"))),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Empty(Difference(Sequence(BasicRelation("po"), BasicRelation("po")), BasicRelation("po"))),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    true
                ),
                arrayOf(
                    Nonempty(Difference(Toid(BasicEventSet("W")), BasicRelation("po"))),
                    Pattern2ExprCompiler(),
                    smallFull.first,
                    smallFull.second,
                    SATGraphSolver(Z3SolverFactory.getInstance().createSolver()),
                    false
                ),
            )
        }
    }
}