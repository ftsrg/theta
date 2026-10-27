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
package hu.bme.mit.theta.core.decl

import com.google.common.base.Preconditions.checkArgument
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.serialization.DeclReferenceSerializer
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.KeepGeneratedSerializer
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

/**
 * Base class for constants. [BasicConstDecl] is a basic constant, [IndexedConstDecl] a constant
 * belonging to a variable for some index (e.g., during unfolding paths).
 */
sealed class ConstDecl<DeclType : Type> : Decl<DeclType>() {

  final override fun toString(): String =
    Utils.lispStringBuilder(DECL_LABEL).add(name).add(type).toString()

  companion object {
    private const val DECL_LABEL = "Const"
  }
}

/** A basic constant declaration that can be directly passed to the SMT solver. */
@Serializable(with = DeclReferenceSerializer::class)
@KeepGeneratedSerializer
class BasicConstDecl<DeclType : Type>
internal constructor(override val name: String, override val type: DeclType) :
  ConstDecl<DeclType>() {

  init {
    checkArgument(name.isNotEmpty())
  }
}

/**
 * A constant declaration that belongs to a variable ([VarDecl]) for a given index. For example,
 * when unfolding a path, each variable will have a new constant for each step of the path.
 */
@Serializable(with = DeclReferenceSerializer::class)
@KeepGeneratedSerializer
class IndexedConstDecl<DeclType : Type>
internal constructor(val varDecl: VarDecl<DeclType>, val index: Int) : ConstDecl<DeclType>() {

  @Transient override val name: String = String.format(NAME_FORMAT, varDecl.name, index)

  override val type: DeclType
    get() = varDecl.type

  init {
    checkArgument(index >= 0)
  }

  companion object {
    private const val NAME_FORMAT = "_%s:%d"
  }
}
