/*
 *  Copyright 2022 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.PrecRefiner
import hu.bme.mit.theta.analysis.expr.refinement.Refutation
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec

class XcfaPrecRefiner<S : ExprState, P : Prec, R : Refutation> (refToPrec: RefutationToPrec<P, R>) :
        PrecRefiner<XcfaState<S>, XcfaAction, XcfaPrec<P>, R> {
    private val refToPrec: RefutationToPrec<P, R> = Preconditions.checkNotNull(refToPrec)

    override fun refine(prec: XcfaPrec<P>, trace: Trace<XcfaState<S>, XcfaAction>, refutation: R): XcfaPrec<P> {
        Preconditions.checkNotNull(trace)
        Preconditions.checkNotNull<Any>(prec)
        Preconditions.checkNotNull<R>(refutation)
        var runningPrec: P = prec.p
        for (i in trace.states.indices) {
            val precFromRef = refToPrec.toPrec(refutation, i)
            runningPrec = refToPrec.join(runningPrec, precFromRef)
        }
        return prec.refine(runningPrec)
    }

    override fun toString(): String {
        return javaClass.simpleName
    }
}
