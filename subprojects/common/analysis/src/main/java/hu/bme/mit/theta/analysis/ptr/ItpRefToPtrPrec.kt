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
package hu.bme.mit.theta.analysis.ptr

import com.google.common.base.Preconditions
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec
import hu.bme.mit.theta.common.Utils

/** Transformer from interpolant refutation to pointer precision. */
class ItpRefToPtrPrec<P : Prec>(private val innerRefToPrec: RefutationToPrec<P, ItpRefutation>) :
  RefutationToPrec<PtrPrec<P>, ItpRefutation> {

  override fun toPrec(refutation: ItpRefutation, index: Int): PtrPrec<P> {
    val newDerefs = refutation[index].dereferences
    val innerPrec = innerRefToPrec.toPrec(refutation, index).repatch()
    return PtrPrec(
      innerPrec,
      newDerefs.flatMap { it.ops }.toSet(),
      if (newDerefs.isEmpty()) 0 else refutation.size() - index,
    )
  }

  override fun join(prec1: PtrPrec<P>, prec2: PtrPrec<P>): PtrPrec<P> {
    Preconditions.checkNotNull(prec1)
    Preconditions.checkNotNull(prec2)
    return PtrPrec(innerRefToPrec.join(prec1.innerPrec, prec2.innerPrec))
  }

  override fun toString(): String {
    return Utils.lispStringBuilder(javaClass.simpleName).aligned().add(innerRefToPrec).toString()
  }
}
