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
package hu.bme.mit.theta.xcfa.witnesses

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.MetaData
import hu.bme.mit.theta.xcfa.model.XCFA

/**
 * The invariant of the [entry]-th content item of a correctness witness. In a transition invariant,
 * each key of [anyPrev] stands for the value of the variable it maps to at an earlier visit of the
 * same evaluation point.
 */
data class InvariantCheck(
  val entry: Int,
  val expr: Expr<BoolType>,
  val anyPrev: Map<VarDecl<*>, VarDecl<*>>,
  val isTransition: Boolean,
)

/**
 * Marks the location where the program is at the evaluation point of [checks]. Passes keep such a
 * location; a copy of it does not carry the checks.
 */
data class InvariantCheckMetaData(val checks: List<InvariantCheck>) : MetaData() {

  override fun combine(other: MetaData): MetaData {
    check(other == this || other is EmptyMetaData) { "Cannot combine $this with $other" }
    return this
  }

  override fun isSubstantial(): Boolean = false

  override fun keepsLocation(): Boolean = true

  override fun withoutLocationMarks(): MetaData = EmptyMetaData
}

val XCFA.hasInvariantChecks: Boolean
  get() = procedures.any { proc -> proc.locs.any { it.metadata is InvariantCheckMetaData } }
