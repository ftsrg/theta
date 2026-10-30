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
package hu.bme.mit.theta.frontend.transformation.model.types.simple

import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType

/**
 * Any received CType instance will either be a NamedType or an Enum (and later a Struct, still
 * under development). The other subclasses are helper classes to provide metadata on the
 * signedness, atomicity, etc. of the type.
 */
sealed class CSimpleType {
  var pointerLevel = 0
    private set

  var isSigned: Boolean? = null

  var isBool = false
    set(value) {
      // _Bool isn't signed, but signed might be the default value in some cases
      if (value) isSigned = false
      field = value
    }

  var isAtomic = false
  var isExtern = false

  /**
   * Whether the declaration carried `static`. Only consulted for a *local* declaration, which it
   * gives static storage duration; at file scope the specifier only affects linkage.
   */
  var isStaticStorage = false
  var isTypedef = false
  var isVolatile = false
  var isShort = false
  var isLong = false
  var isLongLong = false
  var is128 = false
  var isThreadLocal = false
    internal set

  /**
   * According to the grammar, the first declared variable is part of the type (e.g. `int a` will
   * result in a named type `int`, with an associated name `a`)
   */
  var associatedName: String? = null

  /** True when this type is a pointer to a function (e.g. a `typedef int (*h)(int)`). */
  var isFunctionPointer = false

  /**
   * The array dimensions a `typedef` wrote in its own declarator (`typedef int arr_t[2]`).
   *
   * Dimensions normally live on the *declarator*
   * ([hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration.getArrayDimensions]),
   * not on the type -- but a typedef's declarator belongs to the typedef, and every later `arr_t
   * a;` has a declarator of its own with no brackets in it. Without carrying them here the
   * array-ness was simply lost: the variable was created as a scalar and no `alloca` was emitted
   * for it, so the object had no size and the very first element read failed the valid-deref bound
   * check.
   *
   * Carried on the type for the same reason [isFunctionPointer] is -- see
   * `TypedefVisitor#markArrayTypedefs`.
   */
  var typedefArrayDimensions: List<CStatement> = ArrayList()
    set(value) {
      field = ArrayList(value)
    }

  /**
   * Which pointer levels are atomic, innermost first -- one entry per `*`. `_Atomic` attaches to a
   * *level* of a type, not to a declaration, and the level is what decides what may be raced on: an
   * access *through* `p` touches what `p` points at, so `_Atomic int *p` makes `p[i]` race-free
   * while leaving `p` an ordinary variable, and `int * _Atomic p` is the exact opposite. One
   * boolean per declaration cannot tell those apart.
   */
  private val atomicPointers: MutableList<Boolean> = ArrayList()

  /**
   * How many of the pointer levels came from a `*` written in *this* declaration, as opposed to
   * being inherited from the type the specifiers name (a typedef of a pointer, say).
   *
   * The grammar folds the `*` of `int *p` into the declaration specifiers, so by the time a
   * qualifier is applied the type already has a pointer and there is otherwise no way to tell
   * `_Atomic int *p` (the `*` is this declaration's, so `_Atomic` reached only the `int`) from
   * `int_ptr _Atomic p` (the pointer came with the typedef, so `_Atomic` qualifies *it*).
   */
  private var starPointers = 0

  fun incrementPointer() {
    ++pointerLevel
    atomicPointers.add(false)
    ++starPointers
  }

  /** Whether the pointer at this level -- 0 being the innermost -- is itself atomic. */
  fun isAtomicPointer(level: Int): Boolean = level < atomicPointers.size && atomicPointers[level]

  /** `int * _Atomic p`: the `_Atomic` sits after a star, so it is that pointer that is atomic. */
  fun markLastPointerAtomic() {
    if (atomicPointers.isNotEmpty()) {
      atomicPointers[atomicPointers.size - 1] = true
    } else {
      isAtomic = true
    }
  }

  /** `_Atomic(T)`: the whole of T is atomic -- its outermost level, whatever that is. */
  fun markOutermostAtomic() {
    if (pointerLevel > 0) {
      atomicPointers[pointerLevel - 1] = true
    } else {
      isAtomic = true
    }
    // What `_Atomic(T)` yields is a type in its own right. Any `*` after it belongs to the
    // declarator and wraps *around* it, so nothing here is a star of this declaration's.
    starPointers = 0
  }

  /**
   * `_Atomic` written among the declaration specifiers, which qualifies the type they name.
   *
   * That type is the base -- what is written before this declaration's own `*`s -- so for `_Atomic
   * int *p` it is the `int`, and for `int_ptr _Atomic p` (a typedef of `int *`) it is the pointer
   * the typedef brought with it.
   */
  fun applyAtomicQualifier() {
    val inheritedPointers = pointerLevel - starPointers
    if (inheritedPointers > 0) {
      atomicPointers[inheritedPointers - 1] = true
    } else {
      isAtomic = true
    }
  }

  /**
   * The pointers this type already has came *with* it -- it was named by a typedef -- so none of
   * them is a star of the declaration now being read, and a `_Atomic` there qualifies the outermost
   * of them rather than reaching past them to the scalar underneath.
   */
  fun markPointersInherited() {
    starPointers = 0
  }

  fun apply(newCtypes: List<CSimpleType>): CSimpleType {
    var acc = this
    for (newCtype in newCtypes) {
      acc = newCtype.patch(acc)
    }
    return acc
  }

  // we return the patched csimpletype, which might be mutated
  internal abstract fun patch(cSimpleType: CSimpleType): CSimpleType

  /**
   * Returns the base type of the C type e.g. `int* a` will result in a CType of int pointer but the
   * semantic meaning is that it is an int and the declared variable is of pointer type (this is a
   * shortcoming of the grammar)
   */
  open val baseType: CSimpleType
    get() = throw UnsupportedOperationException("Not yet implemented!")

  open val isVoid: Boolean
    get() = false

  open fun copyOf(): CSimpleType =
    throw UnsupportedOperationException("Abstract base class CSimpleType should not be copied")

  open val actualType: CComplexType
    get() =
      throw UnsupportedOperationException("Abstract base class CSimpleType should not be used")

  internal fun setUpCopy(copy: CSimpleType) {
    copy.isAtomic = isAtomic
    copy.isExtern = isExtern
    copy.isStaticStorage = isStaticStorage
    copy.isTypedef = isTypedef
    copy.isVolatile = isVolatile
    copy.isSigned = isSigned
    copy.isShort = isShort
    copy.isLong = isLong
    copy.isBool = isBool
    copy.isLongLong = isLongLong
    copy.is128 = is128
    for (i in 0 until pointerLevel) {
      copy.incrementPointer()
      if (isAtomicPointer(i)) {
        copy.markLastPointerAtomic()
      }
    }
    copy.starPointers = starPointers // a copy inherits what the original inherited
    copy.isFunctionPointer = isFunctionPointer
    // resolveTypedefName hands users a copyOf(), so a typedef's dimensions must survive it.
    copy.typedefArrayDimensions = typedefArrayDimensions
  }
}
