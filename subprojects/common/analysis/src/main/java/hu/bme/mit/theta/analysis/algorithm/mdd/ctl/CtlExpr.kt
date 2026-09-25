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
package hu.bme.mit.theta.analysis.algorithm.mdd.ctl

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType

/** CTL formulas evaluated by [MddCtlChecker]. EX, EU and EG are the primitives. */
sealed interface CtlExpr {

  /** A state predicate. */
  data class Atom(val expr: Expr<BoolType>) : CtlExpr

  /** All reachable states (avoids building a solver-backed node just for `true`). */
  data object Top : CtlExpr

  data class Not(val op: CtlExpr) : CtlExpr

  data class And(val l: CtlExpr, val r: CtlExpr) : CtlExpr

  data class Or(val l: CtlExpr, val r: CtlExpr) : CtlExpr

  data class EX(val op: CtlExpr) : CtlExpr

  /** `E[l U r]`. */
  data class EU(val l: CtlExpr, val r: CtlExpr) : CtlExpr

  data class EG(val op: CtlExpr) : CtlExpr

  data class EF(val op: CtlExpr) : CtlExpr // = E[Top U op]

  data class AX(val op: CtlExpr) : CtlExpr // = !EX !op

  data class AG(val op: CtlExpr) : CtlExpr // = !EF !op

  data class AF(val op: CtlExpr) : CtlExpr // = !EG !op

  /** `A[l U r]` = !(E[!r U (!l & !r)] | EG !r). */
  data class AU(val l: CtlExpr, val r: CtlExpr) : CtlExpr
}
