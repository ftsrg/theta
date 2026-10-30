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
package hu.bme.mit.theta.frontend.transformation.model.types.complex

import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.core.serialization.Tuple2Serializer
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.BitfieldLayout
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.LayoutAttributesSerializer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType
import java.util.Objects
import java.util.stream.Collectors
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

@Serializable
class CStruct
/**
 * @param bitfieldWidths bitfield width per field (-1 for an ordinary, non-bitfield member),
 *   parallel to `fields`. Only meaningful for structs; a union's members all share offset 0
 *   regardless (see [isUnion]), so its layout is not consulted.
 * @param paddings unnamed bitfields, in declaration order (see [Padding])
 * @param attributes layout attributes on the struct itself
 * @param fieldAttributes layout attributes per field, parallel to `fields`; an empty list means
 *   none anywhere
 */
private constructor(
  @Transient override val origin: CSimpleType? = null,
  val fields:
    List<
      @Serializable(with = Tuple2Serializer::class)
      Tuple2<String, @Serializable(with = CComplexTypeReferenceSerializer::class) CComplexType>
    >,
  /**
   * A union's members all start at the same address, so they are all given member offset 0. Since a
   * member access lowers to `__arrays_T[base][offset]` -- an array *per SMT type* -- two members of
   * the same type then genuinely alias (writing one is read back by the other, which is the whole
   * point of the construct), while members of different types land in different arrays and cannot
   * alias at all. Bit-exact punning across differently-typed members needs the flat object layout
   * of AD7 and is rejected rather than answered unsoundly.
   */
  val isUnion: Boolean,
  @Serializable(with = ParseContextSerializer::class) override val parseContext: ParseContext,
  /** Declared bitfield width per field (-1 for an ordinary member); see [overlayWidth]. */
  private val bitfieldWidths: List<Int>,
  /** The unnamed bitfields between this struct's members, in declaration order. */
  val paddings: List<Padding>,
  /** Layout attributes on the struct itself (`packed`, `aligned(n)`). */
  @Serializable(with = LayoutAttributesSerializer::class) val attributes: ObjectLayout.Attributes,
  /** Per-field layout attributes, parallel to [fields]. */
  private val fieldAttributes:
    List<@Serializable(with = LayoutAttributesSerializer::class) ObjectLayout.Attributes>,
) : CInteger() {

  /**
   * An unnamed bitfield: `int : 3;` reserves bits, `int : 0;` closes the current storage unit. It
   * is padding, so it gets no entry in [fields] -- nothing can name it, and giving it a cell would
   * shift every following member's offset in the wired cell model. [ObjectLayout] still has to see
   * it, because it moves where the *next* member sits.
   *
   * @param afterFieldIndex how many named fields precede it, which is what puts it back in
   *   declaration order relative to [fields]
   * @param bitWidth the declared width; 0 means "close the unit"
   * @param baseBits the width of the type it was declared with, i.e. the unit it closes
   */
  @Serializable
  @JvmRecord
  data class Padding(val afterFieldIndex: Int, val bitWidth: Int, val baseBits: Int)

  /**
   * Per-field storage-unit layout, parallel to [fields]. For a struct with no bitfields every field
   * is its own unit and `slots[i].unitIndex() == i` -- byte-for-byte the historical
   * one-cell-per-field model. Consecutive bitfields pack into a shared unit (see [BitfieldLayout]),
   * so a member access lowers to that unit's cell and, for a bitfield, a slice of it.
   */
  @Transient
  private val layout: BitfieldLayout.Layout =
    BitfieldLayout.compute(
      fields.indices.map { i ->
        val bitfieldWidth = if (i < bitfieldWidths.size) bitfieldWidths[i] else -1
        // The base-type width only matters for a bitfield (its unit's packing capacity); for an
        // ordinary member it is unused, so avoid width() -- which throws for aggregate members.
        val baseBits = if (bitfieldWidth >= 0) fields[i].get2().width() else 0
        BitfieldLayout.Member(baseBits, bitfieldWidth)
      }
    )

  constructor(
    origin: CSimpleType?,
    fields: List<Tuple2<String, CComplexType>>,
    parseContext: ParseContext,
  ) : this(origin, fields, false, parseContext)

  constructor(
    origin: CSimpleType?,
    fields: List<Tuple2<String, CComplexType>>,
    union: Boolean,
    parseContext: ParseContext,
  ) : this(origin, fields, union, parseContext, allOrdinary(fields.size))

  constructor(
    origin: CSimpleType?,
    fields: List<Tuple2<String, CComplexType>>,
    union: Boolean,
    parseContext: ParseContext,
    bitfieldWidths: List<Int>,
  ) : this(
    origin,
    java.util.List.copyOf(fields),
    union,
    parseContext,
    java.util.List.copyOf(bitfieldWidths),
    listOf(),
    ObjectLayout.Attributes.NONE,
    listOf(),
  )

  /** The number of storage cells the struct occupies (units, not members). */
  val unitCount: Int
    get() = if (isUnion) 1 else layout.unitCount()

  /**
   * The total bit width of this struct viewed as one packed word, or null if it cannot be.
   *
   * A struct of integers laid end to end -- whether they are bitfields or whole members -- has no
   * substructure to address: its content is just those bits. As a union member it can then share
   * the union's cell with a sibling integer of the same width, which is the register-overlay idiom,
   * in both the forms the kernel and TDX headers use:
   * ```
   *   union { uint64_t raw; struct { uint64_t leaf:16; uint64_t version:8; ... }; };
   *   union { uint64_t raw; struct { uint32_t lo; uint32_t hi; }; };
   * ```
   *
   * Members must all be plain integers: a pointer or a nested aggregate is stored as a base id
   * rather than as its own bits, so it cannot take part in an overlay.
   */
  fun overlayWidth(): Int? {
    if (isUnion || fields.isEmpty()) {
      return null
    }
    var total = 0
    for (i in fields.indices) {
      val width = memberBitWidth(i)
      if (width <= 0) {
        return null
      }
      total += width
    }
    return if (total <= MAX_OVERLAY_BITS) total else null
  }

  /** The bits [offset, offset+width) that [memberName] occupies in the packed word, or null. */
  fun overlaySlotOf(memberName: String): BitfieldLayout.Slot? {
    var offset = 0
    for (i in fields.indices) {
      val width = memberBitWidth(i)
      if (width <= 0) {
        return null
      }
      if (fields[i].get1() == memberName) {
        return BitfieldLayout.Slot(0, offset, width, true)
      }
      offset += width
    }
    return null
  }

  /** A member's width in the packed word: its bitfield width, or its type's full width. */
  private fun memberBitWidth(index: Int): Int {
    val fieldType = fields[index].get2()
    if (fieldType is CStruct) {
      // A nested struct contributes its own bits when it is itself one packed word -- the headers
      // nest anonymous bitfield groups inside the overlay. Otherwise it is stored as a base id and
      // cannot take part.
      return fieldType.overlayWidth() ?: -1
    }
    if (fieldType is CArray || fieldType is CPointer) {
      return -1 // stored as a base id, not as its own bits
    }
    if (fieldType !is CInteger) {
      return -1
    }
    val declared = if (index < bitfieldWidths.size) bitfieldWidths[index] else -1
    return if (declared >= 0) declared else fieldType.width()
  }

  /**
   * The width of the one cell a union's members can share, or null when they cannot share one.
   *
   * A union's members all start at offset 0, so members that are plain integers -- of whatever
   * widths -- are all just the low bits of a single word, and a narrower one is a *slice* of it
   * (see `BitfieldSlice`). That is what lets `union { uint64_t raw; uint32_t half; }` behave as C
   * says rather than being refused as type punning. Pointers count: a pointer value is an integer
   * of pointer width in this model. So does a nested struct that is itself one packed word
   * ([overlayWidth]), which is the register-overlay idiom.
   *
   * Null for the cases a single word genuinely cannot represent: an **array** member is many cells
   * rather than one word, and a **floating-point** member has its own SMT sort, so reading it as
   * bits needs a reinterpretation this model does not have. Those still need the byte-addressed
   * object layout.
   */
  fun unionCellWidth(): Int? {
    if (!isUnion || fields.isEmpty()) {
      return null
    }
    var widest = 0
    for (i in fields.indices) {
      val fieldType = fields[i].get2()
      val width: Int =
        when (fieldType) {
          is CStruct -> fieldType.overlayWidth() ?: return null
          is CArray -> return null
          // A floating-point member would share the cell as its raw IEEE-754 bit pattern, and the
          // machinery for it exists (FpToIeeeBv / FpFromIeeeBv, and the union access path below).
          // It is GATED OFF, though, and a float union is refused rather than answered:
          // fpToIEEEBV is unspecified for NaN, and while a canonical-NaN guard on the write fixes
          // the direct cases, a NaN routed through the integer view and back (`value = NaN; word =
          // ...; value = word`, the pervasive newlib idiom) still yields a spurious non-NaN in the
          // solver, which produced wrong verdicts on float-heavy tasks. Failing loudly beats a
          // wrong answer until the round trip is made sound.
          is CReal -> return null
          // CPointer is a CInteger here: a pointer value is a pointer-wide integer.
          is CInteger -> {
            val declared = declaredBitfieldWidth(i)
            if (declared >= 0) declared else fieldType.width()
          }
          else -> return null
        }
      if (width <= 0 || width > MAX_OVERLAY_BITS) {
        return null
      }
      widest = maxOf(widest, width)
    }
    return widest
  }

  /** The bits [0, width) that [memberName] occupies in a union's shared cell, or null. */
  fun unionSlotOf(memberName: String): BitfieldLayout.Slot? {
    val index = fieldIndexOf(memberName)
    if (index < 0 || unionCellWidth() == null) {
      return null
    }
    val fieldType = fields[index].get2()
    val declared = declaredBitfieldWidth(index)
    val width =
      if (fieldType is CStruct) fieldType.overlayWidth()!!
      else if (declared >= 0) declared else fieldType.width()
    return BitfieldLayout.Slot(0, 0, width, true)
  }

  /** Layout attributes on field [index], never null. */
  fun fieldAttributes(index: Int): ObjectLayout.Attributes =
    if (index >= 0 && index < fieldAttributes.size) fieldAttributes[index]
    else ObjectLayout.Attributes.NONE

  /**
   * The width a member was declared with as a bitfield, or -1 if it is an ordinary member. This is
   * the *declared* width, unlike [slotOf]'s, which reports the cell-packing model.
   */
  fun declaredBitfieldWidth(index: Int): Int =
    if (index >= 0 && index < bitfieldWidths.size) bitfieldWidths[index] else -1

  /** The storage cell index for [memberName], or -1 if it has no field. */
  fun unitOffsetOf(memberName: String): Int {
    val i = fieldIndexOf(memberName)
    return if (i < 0) -1 else layout.slots()[i].unitIndex()
  }

  /** The full slice descriptor for [memberName] (unit, bit offset, width, bitfield?), or null. */
  fun slotOf(memberName: String): BitfieldLayout.Slot? {
    val i = fieldIndexOf(memberName)
    return if (i < 0) null else layout.slots()[i]
  }

  private fun fieldIndexOf(memberName: String): Int {
    for (i in fields.indices) {
      if (fields[i].get1() == memberName) {
        return i
      }
    }
    return -1
  }

  override fun <T, R> accept(visitor: CComplexTypeVisitor<T, R>, param: T): R =
    visitor.visit(this, param)

  override val signedVersion: CInteger
    get() = this

  override val unsignedVersion: CInteger
    get() = this

  val fieldsAsMap: Map<String, CComplexType>
    get() = fields.stream().collect(Collectors.toMap({ it.get1() }, { it.get2() }))

  override val typeName: String
    get() = CUnsignedLong(null, parseContext).typeName

  private fun shape(): List<Tuple2<String, Class<*>>> =
    fields.map { Tuple2.of(it.get1(), it.get2().javaClass) }

  override fun equals(other: Any?): Boolean =
    other != null && javaClass == other.javaClass && shape() == (other as CStruct).shape()

  override fun hashCode(): Int = Objects.hash(javaClass, shape())

  companion object {
    /**
     * Field-list name given to a C11 anonymous struct/union member. Member lookup flattens through
     * fields with this prefix, so `s.a` finds `a` inside `struct S { union { int a; }; }`.
     */
    const val ANONYMOUS_FIELD_PREFIX = "__theta_anon_"

    /** Widest packed word an overlay may occupy; beyond this there is no integer to hold it. */
    private const val MAX_OVERLAY_BITS = 64

    private fun allOrdinary(n: Int): List<Int> = List(n) { -1 }

    /** A struct of copies of the given lists: the parser keeps building the ones it passes. */
    @JvmStatic
    fun of(
      origin: CSimpleType?,
      fields: List<Tuple2<String, CComplexType>>,
      isUnion: Boolean,
      parseContext: ParseContext,
      bitfieldWidths: List<Int>,
      paddings: List<Padding>,
      attributes: ObjectLayout.Attributes,
      fieldAttributes: List<ObjectLayout.Attributes>,
    ): CStruct =
      CStruct(
        origin,
        java.util.List.copyOf(fields),
        isUnion,
        parseContext,
        java.util.List.copyOf(bitfieldWidths),
        java.util.List.copyOf(paddings),
        attributes,
        java.util.List.copyOf(fieldAttributes),
      )
  }
}
