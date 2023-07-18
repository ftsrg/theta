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

package hu.bme.mit.theta.xcfa.analysis

import com.google.common.base.Preconditions
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.PrecRefiner
import hu.bme.mit.theta.analysis.expr.refinement.Refutation
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.changeVars

class XcfaPrecRefiner<S : ExprState, P : Prec, R : Refutation>(refToPrec: RefutationToPrec<P, R>) :
    PrecRefiner<XcfaState<S>, XcfaAction, XcfaPrec<P>, R> {

    private val refToPrec: RefutationToPrec<P, R> = Preconditions.checkNotNull(refToPrec)

    override fun refine(prec: XcfaPrec<P>, trace: Trace<XcfaState<S>, XcfaAction>,
        refutation: R): XcfaPrec<P> {
        Preconditions.checkNotNull(trace)
        Preconditions.checkNotNull<Any>(prec)
        Preconditions.checkNotNull<R>(refutation)
        var runningPrec: P = prec.p
        for (i in trace.states.indices) {
            val reverseLookup = trace.states[i].processes.values.map {
                it.varLookup.map {
                    it.map {
                        Pair(it.value, it.key)
                    }
                }.flatten()
            }.flatten().toMap()
            val additionalLookup = if (i > 0) getTempLookup(
                trace.actions[i - 1].edge.label).entries.associateBy(
                { it.value }) { it.key } else emptyMap()
            val precFromRef = refToPrec.toPrec(refutation, i)
                .changeVars(reverseLookup + additionalLookup)
            runningPrec = refToPrec.join(runningPrec, precFromRef)
        }
        return prec.refine(runningPrec)
    }

    override fun toString(): String {
        return javaClass.simpleName
    }
}

fun <P : Prec> P.changeVars(lookup: Map<VarDecl<*>, VarDecl<*>>): P =
    if (lookup.isEmpty()) this
    else
        when (this) {
            is ExplPrec -> ExplPrec.of(vars.map { it.changeVars(lookup) }) as P
            is PredPrec -> PredPrec.of(preds.map { it.changeVars(lookup) }) as P
            else -> error("Precision type ${this.javaClass} not supported.")
        }

fun <P : Prec> P.addVars(lookups: Collection<Map<VarDecl<*>, VarDecl<*>>>): P =
    if (lookups.isEmpty()) this
    else
        when (this) {
            is ExplPrec -> ExplPrec.of(
                vars.map { lookups.map { lookup -> it.changeVars(lookup) } }.flatten()) as P

            is PredPrec -> PredPrec.of(
                preds.map { lookups.map { lookup -> it.changeVars(lookup) } }.flatten()) as P

            else -> error("Precision type ${this.javaClass} not supported.")
        }
