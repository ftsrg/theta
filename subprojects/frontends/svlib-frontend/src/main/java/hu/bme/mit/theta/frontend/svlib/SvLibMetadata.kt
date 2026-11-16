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
package hu.bme.mit.theta.frontend.svlib

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.xcfa.model.MetaData

class SvLibTagMetadata(tags: Set<String> = setOf(), val procedure: String? = null) : MetaData() {
  val tags = tags.toMutableSet()

  /** set by the [SvLibXcfaBuilder] once the whole script is parsed */
  var liveVars: Set<VarDecl<*>> = setOf()

  override fun combine(other: MetaData) =
    if (other is SvLibTagMetadata)
      SvLibTagMetadata(this.tags + other.tags, this.procedure ?: other.procedure).also {
        it.liveVars = this.liveVars intersect other.liveVars
      }
    else this

  override fun keepsLocation() = tags.isNotEmpty()

  override fun isSubstantial() = tags.isNotEmpty()

  override fun toString() = tags.joinToString(" ")
}

/** Marks the end of a procedure body, where the [tags] annotating the whole body terminate. */
class SvLibProcedureExit(
  val procedure: String,
  val inputs: Set<VarDecl<*>>,
  val outputs: Set<VarDecl<*>>,
) : MetaData() {
  /** set by the [SvLibXcfaBuilder] once the whole script is parsed */
  val tags = mutableSetOf<String>()

  override fun combine(other: MetaData) = this

  override fun keepsLocation() = tags.isNotEmpty()

  override fun isSubstantial() = tags.isNotEmpty()
}

sealed class SvLibWitnessMetadata : MetaData() {
  override fun combine(other: MetaData) = other as? SvLibWitnessMetadata ?: this

  override fun isSubstantial() = true

  /** [initVars]: variables that the call can initialize (outputs and locals) */
  data class InitProcVars(val procedure: String, val initVars: Set<VarDecl<*>>) :
    SvLibWitnessMetadata()

  data class Havoc(val vars: List<VarDecl<*>>) : SvLibWitnessMetadata()

  data class Choice(val index: Int) : SvLibWitnessMetadata()

  data class Annotation(val property: String, val tag: String?) : SvLibWitnessMetadata()
}
