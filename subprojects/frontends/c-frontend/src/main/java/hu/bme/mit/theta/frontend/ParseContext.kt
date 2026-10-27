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
@file:UseSerializers(BigIntegerSerializer::class)

package hu.bme.mit.theta.frontend

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.serialization.BigIntegerSerializer
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.MemoryModelType
import hu.bme.mit.theta.frontend.transformation.CStmtCounter
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.simple.Struct
import java.math.BigInteger
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient
import kotlinx.serialization.UseSerializers

/**
 * The configuration a C program is parsed with, and what parsing found out about it. What later
 * stages read is serialized with the XCFA; the [Transient] rest is only read while parsing (and
 * while c2xcfa builds the XCFA), apart from [metadata], which is carried separately.
 */
@Serializable
class ParseContext {

  @Transient val metadata: FrontendMetadata = FrontendMetadata()

  @Transient val cStmtCounter: CStmtCounter = CStmtCounter()

  @SerialName("arithmeticTraits") private val traits: MutableSet<ArithmeticTrait> = LinkedHashSet()

  val arithmeticTraits: Set<ArithmeticTrait>
    get() = traits.toSet()

  var architecture: ArchitectureType = ArchitectureType.LP64

  var multiThreading: Boolean = false

  var arithmetic: ArithmeticType = ArithmeticType.efficient

  /**
   * Whether [arithmetic] was picked by the frontend from `efficient` rather than chosen by the
   * caller. Only an automatic choice may be revised: if the user asked for integer arithmetic and
   * the program turns out to need bits, that is their answer to live with, but a guess this code
   * made is fair game to correct.
   */
  var isArithmeticAutoSelected: Boolean = false

  var signedWraparound: Boolean = false

  var memoryModel: MemoryModelType = MemoryModelType.multi

  /**
   * Whether the property being verified is a memory-safety one.
   *
   * The frontend emits object-lifetime bookkeeping (see `FunctionVisitor`'s scope-end releases)
   * that only the memory-safety checks read. Under any other property that bookkeeping would be
   * pure cost -- and worse, an observable change to a model nothing asks a question of -- so it is
   * gated on this. The c-frontend module cannot see `MemsafetyPass.enabled`, which is where the
   * same decision is recorded on the pass side; both are set from the same property.
   */
  var isCheckMemsafety: Boolean = false

  // `_Atomic` cells of memory objects by compile-time base id, so the data-race check can skip
  // them:
  // atomicity belongs to the accessed cell, and by analysis time only the base id still names it.
  // Recorded where ids are minted (frontend object layout, ReferenceElimination).
  private val fullyAtomicObjects: MutableSet<BigInteger> = LinkedHashSet()

  private val atomicObjectCells: MutableMap<BigInteger, MutableSet<Int>> = LinkedHashMap()

  /** Which C constructs the program's own code uses, collected once by SourceTraitCollector. */
  var sourceTraits: Map<String, Int> = LinkedHashMap()

  // (parent base, field offset) -> base of the struct-typed subobject kept there, so the race check
  // can follow `(deref (deref parent i) f)` to the object the atomicity is recorded against.
  private val subObjectCells: MutableMap<BigInteger, MutableMap<Int, BigInteger>> = LinkedHashMap()

  // Compile-time base ids of global objects, mapped to the object they are a part of (if any).
  private val staticObjectParents: MutableMap<BigInteger, BigInteger?> = LinkedHashMap()
  private val staticUnions: MutableSet<BigInteger> = LinkedHashSet()

  // Members accessed anywhere in the program, keyed by their (structurally compared) type.
  @Transient private val accessedMembers: MutableMap<CStruct, MutableSet<String>> = LinkedHashMap()
  @Transient private var everyMemberAccessed = false

  /** C return types of the functions called, by name. */
  @Transient val functionReturnTypes: MutableMap<String, CComplexType> = LinkedHashMap()

  /** Keyed by a variable's unique name: witness writers resolve per-thread copies by that name. */
  val variableSources: MutableMap<String, CVariableSource> = LinkedHashMap()

  /** Variables holding a function id: declared function pointers, and functions used as values. */
  @Transient val functionPointerVariables: MutableSet<VarDecl<*>> = LinkedHashSet()

  // Struct and union definitions by tag, and the cached expansions a tag's definition invalidates
  // (see Struct). One program's tags must not resolve in another.
  @Transient val definedStructs: MutableMap<String, Struct> = LinkedHashMap()
  @Transient
  val incompleteStructDependents: MutableMap<String, MutableSet<Struct>> = LinkedHashMap()

  fun addArithmeticTrait(arithmeticTrait: ArithmeticTrait) {
    traits.add(arithmeticTrait)
  }

  /** Records that every cell of the object at base id [base] is `_Atomic`. */
  fun markObjectFullyAtomic(base: BigInteger) {
    fullyAtomicObjects.add(base)
    atomicObjectCells.remove(base) // fully-atomic subsumes any per-cell record
  }

  /** Records that the cell at unit offset [unitOffset] within object [base] is `_Atomic`. */
  fun markObjectAtomicCell(base: BigInteger, unitOffset: Int) {
    if (base in fullyAtomicObjects) return
    atomicObjectCells.getOrPut(base) { LinkedHashSet() }.add(unitOffset)
  }

  /**
   * Whether the cell at [unitOffset] (null when the offset is not a compile-time constant) within
   * the object at base id [base] is `_Atomic`. A fully-atomic object answers true for any offset.
   */
  fun isAtomicObjectCell(base: BigInteger, unitOffset: Int?): Boolean {
    if (base in fullyAtomicObjects) return true
    if (unitOffset == null) return false
    return atomicObjectCells[base]?.contains(unitOffset) == true
  }

  /**
   * Records that cell [unitOffset] of object [parentBase] holds the base id of subobject [subBase].
   */
  fun recordSubObjectCell(parentBase: BigInteger, unitOffset: Int, subBase: BigInteger) {
    subObjectCells.getOrPut(parentBase) { LinkedHashMap() }[unitOffset] = subBase
  }

  /**
   * The base id of the subobject held in cell [unitOffset] of object [parentBase], or null when no
   * subobject is recorded there.
   */
  fun subObjectBaseAt(parentBase: BigInteger, unitOffset: Int?): BigInteger? =
    unitOffset?.let { subObjectCells[parentBase]?.get(it) }

  /**
   * Records that [base] is the compile-time base id of a global object, stored within the object
   * [parent] (null for a top-level object).
   */
  fun recordStaticObject(base: BigInteger, union: Boolean, parent: BigInteger?) {
    staticObjectParents[base] = parent
    if (union) staticUnions.add(base)
  }

  fun isStaticObject(base: BigInteger): Boolean = staticObjectParents.containsKey(base)

  /** Records that member [member] of [type] is accessed somewhere in the program. */
  fun markMemberAccessed(type: CStruct, member: String) {
    accessedMembers.getOrPut(type) { LinkedHashSet() }.add(member)
  }

  /** Records that an access could not be attributed to a type, so every member may be read. */
  fun markEveryMemberAccessed() {
    everyMemberAccessed = true
  }

  fun isMemberAccessed(type: CStruct, member: String): Boolean =
    everyMemberAccessed || accessedMembers[type]?.contains(member) == true

  fun isAnyMemberAccessed(type: CStruct): Boolean =
    everyMemberAccessed || accessedMembers.containsKey(type)

  /**
   * The outermost union the static object [base] is a part of (itself included), or null when there
   * is none.
   */
  fun enclosingStaticUnion(base: BigInteger): BigInteger? {
    var union: BigInteger? = null
    var current: BigInteger? = base
    while (current != null) {
      if (current in staticUnions) union = current
      current = staticObjectParents[current]
    }
    return union
  }
}
