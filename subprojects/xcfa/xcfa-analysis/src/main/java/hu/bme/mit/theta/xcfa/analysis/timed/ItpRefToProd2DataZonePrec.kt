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

package hu.bme.mit.theta.xcfa.analysis.timed

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec
import hu.bme.mit.theta.analysis.prod2.Prod2Prec
import hu.bme.mit.theta.analysis.zone.ZonePrec

class ItpRefToProd2DataZonePrec<P : Prec>(
    private val itpRefToPrec : RefutationToPrec<P, ItpRefutation>
) : RefutationToPrec<Prod2Prec<P, ZonePrec>, ItpRefutation> {

    override fun toPrec(refutation: ItpRefutation, index: Int): Prod2Prec<P, ZonePrec> =
        Prod2Prec.of(
            itpRefToPrec.toPrec(refutation, index),
            ZonePrec.of(listOf())
        )

    override fun join(prec1: Prod2Prec<P, ZonePrec>, prec2: Prod2Prec<P, ZonePrec>): Prod2Prec<P, ZonePrec> =
        Prod2Prec.of(
            itpRefToPrec.join(prec1.prec1, prec2.prec1),
            ZonePrec.of(prec1.prec2.vars + prec2.prec2.vars)
        )
}
