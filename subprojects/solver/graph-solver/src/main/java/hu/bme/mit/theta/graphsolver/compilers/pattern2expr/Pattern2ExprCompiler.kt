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

package hu.bme.mit.theta.graphsolver.compilers.pattern2expr

import hu.bme.mit.theta.common.Tuple
import hu.bme.mit.theta.common.Tuple1
import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decls.Const
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.graphsolver.ThreeVL
import hu.bme.mit.theta.graphsolver.compilers.GraphPatternCompiler
import hu.bme.mit.theta.graphsolver.patterns.constraints.*
import hu.bme.mit.theta.graphsolver.patterns.patterns.*
import java.util.*
import kotlin.jvm.optionals.getOrNull

class Pattern2ExprCompiler : GraphPatternCompiler<Expr<BoolType>, Map<Tuple, Expr<BoolType>>> {

    private val events = ArrayList<Int>()
    private val facts = LinkedHashMap<Pair<String, Tuple>, ThreeVL>()
    private val namedLookup = LinkedHashMap<Pair<String, Tuple>, ConstDecl<BoolType>>()

    private val transitiveConstraints = ArrayList<Expr<BoolType>>()
    override fun addEvents(events: List<Int>) {
        this.events.addAll(events)
    }

    override fun addFacts(edges: Map<Pair<String, Tuple>, ThreeVL>) {
        this.facts.putAll(edges)
    }

    @OptIn(ExperimentalStdlibApi::class)
    override fun getCompleteGraph(namedPatterns: Set<GraphPattern>,
        model: Valuation): Pair<List<Int>, Map<Pair<String, Tuple>, ThreeVL>> {
        val ret = LinkedHashMap<Pair<String, Tuple>, ThreeVL>()
        ret.putAll(facts)
        ret.putAll(namedLookup.map { n ->
            model.eval(n.value).map { Pair(n.key, if (it == True()) ThreeVL.TRUE else ThreeVL.FALSE) }.getOrNull()
        }.filterNotNull().toMap())
        ret.putAll(namedPatterns.map { pattern ->
            pattern.accept(this).map { (tup, expr) ->
                Pair(Pair(pattern.patternName!!, tup), if (expr.eval(model) == True()) ThreeVL.TRUE else ThreeVL.FALSE)
            }
        }.flatten().toMap())
        return Pair(events, ret)
    }

    override fun compile(acyclic: Acyclic): Expr<BoolType> =
        Irreflexive(TransitiveClosure(acyclic.constrainedRule)).accept(this)

    override fun compile(cyclic: Cyclic): Expr<BoolType> =
        Reflexive(TransitiveClosure(cyclic.constrainedRule)).accept(this)

    override fun compile(empty: Empty): Expr<BoolType> {
        val compiledRule = empty.constrainedRule.accept(this)
        val ret = And(Not(Or(compiledRule.values)), And(transitiveConstraints))
        transitiveConstraints.clear()
        return ret
    }

    override fun compile(nonempty: Nonempty): Expr<BoolType> {
        val compiledRule = nonempty.constrainedRule.accept(this)
        val ret = And(Or(compiledRule.values), And(transitiveConstraints))
        transitiveConstraints.clear()
        return ret
    }

    override fun compile(reflexive: Reflexive): Expr<BoolType> {
        val compiled = reflexive.constrainedRule.accept(this)
        val ret = And(Or(events.map { compiled[Tuple2.of(it, it)] }), And(transitiveConstraints))
        transitiveConstraints.clear()
        return ret
    }

    override fun compile(irreflexive: Irreflexive): Expr<BoolType> {
        val compiled = irreflexive.constrainedRule.accept(this)
        val ret = And(Not(Or(events.map { compiled[Tuple2.of(it, it)] })), And(transitiveConstraints))
        transitiveConstraints.clear()
        return ret
    }

    override fun compile(pattern: CartesianProduct): Map<Tuple, Expr<BoolType>> {
        val op1Compiled = pattern.op1.accept(this)
        val op2Compiled = pattern.op2.accept(this)

        val ret = events.map { a ->
            events.map { b ->
                Pair(Tuple2.of(a, b), And(op1Compiled[Tuple1.of(a)], op2Compiled[Tuple1.of(b)]))
            }
        }
        return ret.flatten().toMap()
    }

    override fun compile(pattern: Complement): Map<Tuple, Expr<BoolType>> =
        pattern.op.accept(this).map { Pair(it.key, Not(it.value)) }.toMap()

    override fun compile(pattern: ComplementNode): Map<Tuple, Expr<BoolType>> =
        pattern.op.accept(this).map { Pair(it.key, Not(it.value)) }.toMap()

    override fun compile(pattern: Difference): Map<Tuple, Expr<BoolType>> {
        val op1Compiled = pattern.op1.accept(this)
        val op2Compiled = pattern.op2.accept(this)

        val ret = events.map { a ->
            events.map { b ->
                Pair(Tuple2.of(a, b), And(op1Compiled[Tuple2.of(a, b)], Not(op2Compiled[Tuple2.of(a, b)])))
            }
        }
        return ret.flatten().toMap()
    }

    override fun compile(pattern: DifferenceNode): Map<Tuple, Expr<BoolType>> {
        val op1Compiled = pattern.op1.accept(this)
        val op2Compiled = pattern.op2.accept(this)

        val ret = events.map { a -> Pair(Tuple1.of(a), And(op1Compiled[Tuple1.of(a)], Not(op2Compiled[Tuple1.of(a)]))) }
        return ret.toMap()
    }

    override fun compile(pattern: Domain): Map<Tuple, Expr<BoolType>> {
        val opCompiled = pattern.op.accept(this)

        val ret = events.map { a -> Pair(Tuple1.of(a), Or(events.map { b -> opCompiled[Tuple2.of(a, b)] })) }
        return ret.toMap()
    }

    override fun compile(pattern: EmptyRel): Map<Tuple, Expr<BoolType>> {
        return events.map { a -> events.map { b -> Pair(Tuple2.of(a, b), False()) } }.flatten().toMap()
    }

    override fun compile(pattern: EmptySet): Map<Tuple, Expr<BoolType>> {
        return events.associate { a -> Pair(Tuple1.of(a), False()) }
    }

    override fun compile(pattern: IdentityClosure): Map<Tuple, Expr<BoolType>> {
        val opCompiled = pattern.op.accept(this)
        return events.map { a ->
            events.map { b ->
                Pair(Tuple2.of(a, b), if (a == b) True() else checkNotNull(opCompiled[Tuple2.of(a, b)]))
            }
        }.flatten().toMap()
    }

    override fun compile(pattern: Intersection): Map<Tuple, Expr<BoolType>> {
        val op1Compiled = pattern.op1.accept(this)
        val op2Compiled = pattern.op2.accept(this)

        val ret = events.map { a ->
            events.map { b ->
                Pair(Tuple2.of(a, b), And(op1Compiled[Tuple2.of(a, b)], op2Compiled[Tuple2.of(a, b)]))
            }
        }
        return ret.flatten().toMap()
    }

    override fun compile(pattern: IntersectionNode): Map<Tuple, Expr<BoolType>> {
        val op1Compiled = pattern.op1.accept(this)
        val op2Compiled = pattern.op2.accept(this)

        val ret = events.map { a -> Pair(Tuple1.of(a), And(op1Compiled[Tuple1.of(a)], op2Compiled[Tuple1.of(a)])) }
        return ret.toMap()
    }

    override fun compile(pattern: Inverse): Map<Tuple, Expr<BoolType>> {
        val opCompiled = pattern.op.accept(this)
        return events.map { a -> events.map { b -> Pair(Tuple2.of(a, b), checkNotNull(opCompiled[Tuple2.of(b, a)])) } }
            .flatten()
            .toMap()
    }

    override fun compile(pattern: Range): Map<Tuple, Expr<BoolType>> {
        val opCompiled = pattern.op.accept(this)

        val ret = events.map { a -> Pair(Tuple1.of(a), Or(events.map { b -> opCompiled[Tuple2.of(a, b)] })) }
        return ret.toMap()
    }

    override fun compile(pattern: ReflexiveTransitiveClosure): Map<Tuple, Expr<BoolType>> {
        val opCompiled = pattern.op.accept(this)
        val uuid = Random().nextInt()
        val consts = events.map { a ->
            events.map { b ->
                val const = if (pattern.patternName != null) {
                    val const = namedLookup[Pair(pattern.patternName!!, Tuple2.of(a, b))] ?: Const(
                        "RTC_" + uuid + "_" + a + "_" + b, Bool())
                    namedLookup[Pair(pattern.patternName!!, Tuple2.of(a, b))] = const
                    const
                } else {
                    Const("RTC_" + uuid + "_" + a + "_" + b, Bool())
                }
                Pair(Tuple2.of(a, b), const)
            }
        }.flatten().toMap()

        val constraints = And(events.map { a ->
            events.map { b ->
                Iff(Or(opCompiled[Tuple2.of(a, b)], Or(events.map { c ->
                    Or(
                        And(opCompiled[Tuple2.of(a, c)], checkNotNull(consts[Tuple2.of(c, b)]).ref),
                        And(checkNotNull(consts[Tuple2.of(a, c)]).ref, opCompiled[Tuple2.of(c, b)])
                    )
                })), checkNotNull(consts[Tuple2.of(a, b)]).ref)
            }
        }.flatten())
        transitiveConstraints.add(constraints)
        val ret = events.map { a ->
            events.map { b ->
                Pair(Tuple2.of(a, b), if (a == b) True() else checkNotNull(consts[Tuple2.of(a, b)]).ref)
            }
        }
        return ret.flatten().toMap()
    }

    override fun compile(pattern: Self): Map<Tuple, Expr<BoolType>> =
        pattern.op.accept(this)

    override fun compile(pattern: Sequence): Map<Tuple, Expr<BoolType>> {
        val op1Compiled = pattern.op1.accept(this)
        val op2Compiled = pattern.op2.accept(this)

        val ret = events.map { a ->
            events.map { b ->
                Pair(Tuple2.of(a, b), Or(events.filter { c -> a != c && b != c }.map { c ->
                    And(op1Compiled[Tuple2.of(a, c)], op2Compiled[Tuple2.of(c, b)])
                }))
            }
        }
        return ret.flatten().toMap()
    }

    override fun compile(pattern: Toid): Map<Tuple, Expr<BoolType>> {
        val opCompiled = pattern.op.accept(this)
        val ret = events.map { a ->
            events.map { b ->
                Pair(Tuple2.of(a, b), if (a == b) checkNotNull(opCompiled[Tuple1.of(a)]) else False())
            }
        }
        return ret.flatten().toMap()
    }

    override fun compile(pattern: TransitiveClosure): Map<Tuple, Expr<BoolType>> {
        val uuid = Random().nextInt()
        val opCompiled = pattern.op.accept(this)
        val consts = events.map { a ->
            events.map { b ->
                val const = if (pattern.patternName != null) {
                    val const = namedLookup[Pair(pattern.patternName!!, Tuple2.of(a, b))] ?: Const(
                        "TC_" + uuid + "_" + a + "_" + b, Bool())
                    namedLookup[Pair(pattern.patternName!!, Tuple2.of(a, b))] = const
                    const
                } else {
                    Const("TC_" + uuid + "_" + a + "_" + b, Bool())
                }
                Pair(Tuple2.of(a, b), const)
            }
        }.flatten().toMap()

        val constraints = And(events.map { a ->
            events.map { b ->
                Iff(Or(opCompiled[Tuple2.of(a, b)], Or(events.filter { c -> a != c && b != c }.map { c ->
                    Or(
                        And(opCompiled[Tuple2.of(a, c)], checkNotNull(consts[Tuple2.of(c, b)]).ref),
                        And(checkNotNull(consts[Tuple2.of(a, c)]).ref, opCompiled[Tuple2.of(c, b)])
                    )
                })), checkNotNull(consts[Tuple2.of(a, b)]).ref)
            }
        }.flatten())
        transitiveConstraints.add(constraints)
        val ret = events.map { a ->
            events.map { b ->
                Pair(Tuple2.of(a, b), checkNotNull(consts[Tuple2.of(a, b)]).ref)
            }
        }
        return ret.flatten().toMap()
    }

    override fun compile(pattern: Union): Map<Tuple, Expr<BoolType>> {
        val op1Compiled = pattern.op1.accept(this)
        val op2Compiled = pattern.op2.accept(this)

        val ret = events.map { a ->
            events.map { b ->
                Pair(Tuple2.of(a, b), Or(op1Compiled[Tuple2.of(a, b)], op2Compiled[Tuple2.of(a, b)]))
            }
        }
        return ret.flatten().toMap()
    }

    override fun compile(pattern: UnionNode): Map<Tuple, Expr<BoolType>> {
        val op1Compiled = pattern.op1.accept(this)
        val op2Compiled = pattern.op2.accept(this)

        val ret = events.map { a -> Pair(Tuple1.of(a), And(op1Compiled[Tuple1.of(a)], op2Compiled[Tuple1.of(a)])) }
        return ret.toMap()
    }

    override fun compile(pattern: BasicEventSet): Map<Tuple, Expr<BoolType>> {
        return events.associate { a ->
            Pair(Tuple1.of(a),
                when (facts[Pair(pattern.name, Tuple1.of(a))]) {
                    ThreeVL.FALSE -> False()
                    ThreeVL.TRUE -> True()
                    ThreeVL.UNKNOWN, null -> namedLookup.getOrElse(Pair(pattern.name, Tuple1.of(a))) {
                        val cnst = Const(pattern.name + "_" + a, Bool())
                        namedLookup[Pair(pattern.name, Tuple1.of(a))] = cnst
                        cnst
                    }.ref
                })
        }
    }

    override fun compile(pattern: BasicRelation): Map<Tuple, Expr<BoolType>> {
        return events.map { a ->
            events.map { b ->
                Pair(Tuple2.of(a, b),
                    when (facts[Pair(pattern.name, Tuple2.of(a, b))]) {
                        ThreeVL.FALSE -> False()
                        ThreeVL.TRUE -> True()
                        ThreeVL.UNKNOWN, null -> namedLookup.getOrElse(Pair(pattern.name, Tuple2.of(a, b))) {
                            val cnst = Const(pattern.name + "_" + a + "-" + b, Bool())
                            namedLookup[Pair(pattern.name, Tuple2.of(a, b))] = cnst
                            cnst
                        }.ref
                    })
            }
        }.flatten().toMap()
    }
}