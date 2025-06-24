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
package hu.bme.mit.theta.core.decl

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

/**
 * Represents a variable declaration. Variables cannot be directly passed to the SMT solver, they
 * must be replaced with constants for a given index ([IndexedConstDecl]). See also
 * [hu.bme.mit.theta.core.utils.PathUtils].
 *
 * @param <DeclType>
 */
@Serializable
@SerialName(VarDecl.DECL_LABEL)
data class VarDecl<DeclType : Type>(override val name: String, override val type: DeclType) :
  Decl<DeclType>() {

  companion object {

    internal const val DECL_LABEL: String = "var"

    fun <T : Type> copyOf(from: VarDecl<T>): VarDecl<T> = VarDecl(from.name, from.type)
  }

  @Transient private val indexToConst = mutableMapOf<Int, IndexedConstDecl<DeclType>>()

  fun getConstDecl(index: Int): IndexedConstDecl<DeclType> {
    require(index >= 0) { "Index must be non-negative" }
    return indexToConst.getOrPut(index) { IndexedConstDecl(this, index) }
  }

  override fun toString(): String =
    Utils.lispStringBuilder(DECL_LABEL).add(name).add(type).toString()
}
