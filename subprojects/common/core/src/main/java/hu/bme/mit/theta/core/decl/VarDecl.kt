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
import hu.bme.mit.theta.common.collection.CollectionUtil
import hu.bme.mit.theta.core.type.RefExpr
import hu.bme.mit.theta.core.type.Type

/**
 * Represents a variable declaration. Variables cannot be directly passed to the SMT solver, they
 * must be replaced with constants for a given index ([IndexedConstDecl]). See also
 * [hu.bme.mit.theta.core.utils.PathUtils].
 */
open class VarDecl<DeclType : Type> internal constructor(name: String, type: DeclType) :
  Decl<DeclType>(name, type) {

  private val indexToConst: MutableMap<Int, IndexedConstDecl<DeclType>> = CollectionUtil.createMap()

  fun getConstDecl(index: Int): IndexedConstDecl<DeclType> {
    checkArgument(index >= 0)
    return indexToConst.getOrPut(index) { IndexedConstDecl(this, index) }
  }

  override fun toString(): String =
    Utils.lispStringBuilder(DECL_LABEL).add(name).add(type).toString()

  companion object {
    private const val DECL_LABEL = "var"

    @JvmStatic
    fun <DeclType : Type> copyOf(from: VarDecl<DeclType>): VarDecl<DeclType> =
      VarDecl(from.name, from.type)
  }
}

class IndexedVarDecl<DeclType : Type>
internal constructor(name: String, val original: VarDecl<DeclType>) :
  VarDecl<DeclType>(name, original.type) {

  val const: ConstDecl<DeclType> = Decls.Const(name, original.type)

  val constRef: RefExpr<DeclType> = RefExpr.of(const)

  companion object {
    @JvmStatic
    fun <DeclType : Type> of(name: String, original: VarDecl<DeclType>): IndexedVarDecl<DeclType> =
      IndexedVarDecl(name, original)
  }
}
