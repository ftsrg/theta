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

class SvLibTagMetadata(val tags: Set<String> = setOf(), val procedure: String? = null) :
  MetaData() {
  override fun combine(other: MetaData) =
    if (other is SvLibTagMetadata)
      SvLibTagMetadata(this.tags + other.tags, this.procedure ?: other.procedure)
    else this

  override fun keepsLocation() = tags.isNotEmpty()

  override fun isSubstantial() = tags.isNotEmpty()

  override fun toString() = tags.joinToString(" ")
}

sealed class SvLibWitnessMetadata : MetaData() {
  override fun combine(other: MetaData) = other as? SvLibWitnessMetadata ?: this

  override fun isSubstantial() = true

  data class InitProcVars(val procedure: String) : SvLibWitnessMetadata()

  data class Havoc(val vars: List<VarDecl<*>>) : SvLibWitnessMetadata()

  data class Choice(val index: Int) : SvLibWitnessMetadata()

  data class Annotation(val property: String, val tag: String?) : SvLibWitnessMetadata()
}
