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

import com.google.common.base.Preconditions.checkNotNull
import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.Logger.Level
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout
import java.util.ArrayDeque

class Struct
private constructor(
  private val name: String?,
  /**
   * A union: every member starts at the same address. Members are therefore all given offset 0, so
   * that two members of the same type genuinely alias (see CStruct#isUnion).
   */
  val isUnion: Boolean,
  parseContext: ParseContext,
  private val uniqueWarningLogger: Logger,
  /**
   * If this instance is a copy (see [copyOf]) of another [Struct], this points to the specific
   * struct definition instance it was copied from, bound once at copy-creation time. `null` means
   * this instance IS a canonical struct definition (i.e. either a fresh,
   * possibly-still-being-parsed struct, or one no longer reachable through [definedTypes] because
   * it was superseded by a later redefinition of the same tag).
   *
   * Field lookups ([resolvedFields]) are delegated through this reference instead of
   * value-snapshotting the field map at copy time. This matters for self-referential structs (e.g.
   * an intrusive linked list's `struct list_head *next;` field): the pointer field's type is a copy
   * created WHILE the enclosing struct is still being parsed, i.e. before its own fields (including
   * possibly `next` itself) have all been added. Snapshotting at that point would freeze an empty
   * (or partial) field map into the copy forever. Delegating instead means the copy always sees the
   * canonical definition's current (eventually complete) field map. Binding to the specific object
   * (rather than re-resolving the tag name through [definedTypes] on every access) also means a
   * later, genuine redefinition of the same tag name does not retroactively change the fields
   * already-created copies resolve to.
   */
  private val canonicalRef: Struct?,
) : NamedType(parseContext, if (isUnion) "union" else "struct", uniqueWarningLogger) {

  private val fields: MutableMap<String, CDeclaration> = LinkedHashMap()

  private var currentlyBeingBuilt = false

  /**
   * Set while this tag's `{ ... }` body is being read, i.e. between the first member and the last
   * (see [beginDefinition]). A tag in that state is just as incomplete as one with no body at all:
   * expanding it yields whatever members have been seen so far, and the rest arrive afterwards. It
   * matters because a member can pull the *enclosing* tag back in mid-definition -- `struct cert_st
   * { ...; RSA *(*cb)(SSL *ssl, int, int); ...; CERT_PKEY pkeys[5]; }` resolves the typedef `SSL`
   * while reading that parameter, and `struct ssl_st` has a `struct cert_st *cert` member, so
   * `cert_st` is expanded (and cached into `ssl_st`) with only its first five members. Without this
   * flag that half-expansion is treated as complete and never invalidated, so `(s->cert)->pkeys`
   * fails with "field not found" for the rest of the run.
   */
  private var definitionInProgress = false

  /**
   * The expanded field list of the *canonical* definition, shared by every copy. A nested struct
   * type re-expands its whole subtree on each use; without this cache the expansion is exponential
   * in nesting depth (large LDV kernel headers ran out of heap inside it). Invalidated on
   * [addField], so a still-growing definition never serves a stale snapshot.
   */
  private var cachedActualFields: List<Tuple2<String, CComplexType>>? = null

  /** Unnamed bitfields, in declaration order; see [addPadding]. */
  private val paddings: MutableList<CStruct.Padding> = ArrayList()

  /** `packed` / `aligned(n)` on the struct itself; see [setLayoutAttributes]. */
  private var layoutAttributes: ObjectLayout.Attributes = ObjectLayout.Attributes.NONE

  internal constructor(
    name: String?,
    parseContext: ParseContext,
    uniqueWarningLogger: Logger,
  ) : this(name, false, parseContext, uniqueWarningLogger)

  internal constructor(
    name: String?,
    union: Boolean,
    parseContext: ParseContext,
    uniqueWarningLogger: Logger,
  ) : this(name, union, parseContext, uniqueWarningLogger, null) {
    if (name != null) {
      definedTypes[tagOf(name, union)] = this
    }
  }

  private constructor(
    from: Struct
  ) : this(from.name, from.isUnion, from.parseContext, from.uniqueWarningLogger, from.canonical())

  /** The struct definition instance this instance's fields should be resolved from. */
  private fun canonical(): Struct = canonicalRef ?: this

  /** The authoritative, possibly still-growing, field map for this struct (see [canonicalRef]). */
  private fun resolvedFields(): Map<String, CDeclaration> = canonical().fields

  /** Whether this tag has been given a body yet (see the forward-declaration path). */
  fun hasFields(): Boolean = canonical().fields.isNotEmpty()

  /**
   * The tag as written (`struct device_private`), for diagnostics. An unresolved member access
   * reports only the field name, which cannot tell "resolved the wrong struct" apart from "right
   * struct, no fields" -- and that distinction is what a field-less struct error hinges on.
   */
  val tagName: String
    get() = (if (isUnion) "union " else "struct ") + (name ?: "<anonymous>")

  /**
   * Mark the start of this tag's member list; see [definitionInProgress]. Paired with
   * [endDefinition].
   */
  fun beginDefinition() {
    canonical().definitionInProgress = true
  }

  /** Mark the member list finished; see [definitionInProgress]. */
  fun endDefinition() {
    canonical().definitionInProgress = false
  }

  fun addField(decl: CDeclaration) {
    fields[checkNotNull(decl.name)] = checkNotNull(decl)
    cachedActualFields = null
    canonical().cachedActualFields = null
    // Anything that cached an expansion containing this tag while it was still field-less is now
    // stale. The entry is kept rather than removed: fields arrive one at a time, and a dependent
    // could re-cache between two of them.
    if (name != null) {
      incompleteDependents[tagOf(name, isUnion)]?.forEach { it.cachedActualFields = null }
    }
  }

  /**
   * Record an unnamed bitfield (`int : 3;`, `int : 0;`). It is padding, so it gets no field -- but
   * it moves where the next member sits, which [CStruct.Padding] preserves. Stored on the canonical
   * definition, like the fields themselves.
   */
  fun addPadding(bitWidth: Int, baseBits: Int) {
    val canonical = canonical()
    canonical.paddings.add(CStruct.Padding(canonical.fields.size, bitWidth, baseBits))
  }

  /** Layout attributes (`packed`, `aligned(n)`) on the struct itself. */
  fun setLayoutAttributes(attributes: ObjectLayout.Attributes) {
    canonical().layoutAttributes = attributes
  }

  override val actualType: CComplexType
    get() {
      if (currentlyBeingBuilt) {
        uniqueWarningLogger.write(
          Level.INFO,
          "WARNING: self-embedded structs! Using long as a placeholder\n",
        )
        var placeholder = CComplexType.getSignedInt(parseContext)
        for (i in 0 until pointerLevel) {
          placeholder = CPointer(this, placeholder, parseContext)
        }
        return placeholder
      }
      currentlyBeingBuilt = true
      val canonical = canonical()
      // Expanding a tag whose body is not (fully) parsed yet yields a CStruct missing members --
      // unavoidable, they have not been read. Report it to the expansion in progress so that
      // whatever caches this result can be invalidated when the remaining members arrive. Both an
      // undefined tag and one whose `{ ... }` is still being read count (see definitionInProgress).
      if (
        name != null &&
          (canonical.fields.isEmpty() || canonical.definitionInProgress) &&
          expansionFrames.isNotEmpty()
      ) {
        expansionFrames.peek().add(tagOf(name, isUnion))
      }
      var actualFields = canonical.cachedActualFields
      if (actualFields == null) {
        val frame: MutableSet<String> = LinkedHashSet()
        expansionFrames.push(frame)
        val expanded = ArrayList<Tuple2<String, CComplexType>>()
        try {
          resolvedFields().forEach { (s, cDeclaration) ->
            expanded.add(Tuple2.of(s, cDeclaration.actualType))
          }
        } finally {
          expansionFrames.pop()
        }
        canonical.cachedActualFields = expanded
        for (tag in frame) {
          incompleteDependents.computeIfAbsent(tag) { LinkedHashSet() }.add(canonical)
        }
        // Ancestors depend on these tags too: their own expansion contains this one.
        if (expansionFrames.isNotEmpty()) {
          expansionFrames.peek().addAll(frame)
        }
        actualFields = expanded
      }
      currentlyBeingBuilt = false

      // Carry each field's bitfield width (parallel to actualFields) so CStruct can pack
      // consecutive bitfields into shared storage units. resolvedFields() is insertion-ordered,
      // the same order actualFields was built in.
      val bitfieldWidths = resolvedFields().values.map { it.bitfieldWidth }

      // Layout attributes and unnamed-bitfield padding live on the canonical definition too: a copy
      // is made mid-parse (see canonicalRef) and would otherwise freeze an empty list.
      val fieldAttributes = resolvedFields().values.map { it.layoutAttributes }

      var type: CComplexType =
        CStruct(
          this,
          actualFields,
          isUnion,
          parseContext,
          bitfieldWidths,
          canonical().paddings,
          canonical().layoutAttributes,
          fieldAttributes,
        )
      if (isAtomic) {
        type.setAtomic()
      }
      for (i in 0 until pointerLevel) {
        type = CPointer(this, type, parseContext)
        if (isAtomicPointer(i)) {
          type.setAtomic()
        }
      }
      return type
    }

  override val baseType: CSimpleType
    get() = this

  override val isVoid: Boolean
    get() = false

  override fun copyOf(): CSimpleType = Struct(this).also { setUpCopy(it) }

  companion object {
    /**
     * The tags expanded while still field-less during the expansion currently in progress, one set
     * per nesting level (see [actualType]). A level's set is merged into its parent's when it
     * finishes, so an enclosing struct learns about incomplete tags found anywhere beneath it, not
     * just among its own immediate members.
     */
    private val expansionFrames = ArrayDeque<MutableSet<String>>()

    /**
     * Tag → the canonical structs whose cached expansion baked in that tag while it was still
     * field-less. [addField] clears exactly these when the tag is finally defined.
     *
     * This exists because `addField` invalidating only its *own* cache is not enough: in a
     * CIL-preprocessed kernel source `struct device` expands `struct device_private *p` hundreds of
     * thousands of characters before that tag is defined, so `struct device` keeps a pointer to a
     * field-less struct forever and every `(dev->p)->driver_data` fails with "available fields are:
     * []".
     *
     * Targeted invalidation, rather than the two blunter options, both of which were measured:
     * declining to cache an incomplete expansion at all sounds narrow ("incomplete tags are rare")
     * but is not -- forward declarations are pervasive in these sources, so nearly nothing cached
     * and three LDV files went from ~19s to `OutOfMemoryError`, the expansion being exponential in
     * nesting depth. A global generation counter invalidating every cache per `addField` fails the
     * same way for the whole declaration phase.
     */
    private val incompleteDependents: MutableMap<String, MutableSet<Struct>> = LinkedHashMap()

    private val definedTypes: MutableMap<String, Struct> = LinkedHashMap()

    @JvmStatic fun getByName(name: String): Struct? = getByName(name, false)

    /** `struct X` and `union X` are distinct types, so the tag alone does not identify one. */
    @JvmStatic
    fun getByName(name: String, union: Boolean): Struct? = definedTypes[tagOf(name, union)]

    private fun tagOf(name: String, union: Boolean): String =
      (if (union) "union " else "struct ") + name
  }
}
