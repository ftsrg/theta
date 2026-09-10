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
package hu.bme.mit.theta.frontend.transformation.model.types.simple;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public class Struct extends NamedType {

    private final Map<String, CDeclaration> fields;
    private final String name;
    private final Logger uniqueWarningLogger;

    /**
     * A union: every member starts at the same address. Members are therefore all given offset 0,
     * so that two members of the same type genuinely alias (see CStruct#isUnion).
     */
    private final boolean union;

    /**
     * If this instance is a copy (see {@link #copyOf()}) of another {@link Struct}, this points to
     * the specific struct definition instance it was copied from, bound once at copy-creation time.
     * {@code null} means this instance IS a canonical struct definition (i.e. either a fresh,
     * possibly-still-being-parsed struct, or one no longer reachable through {@link #definedTypes}
     * because it was superseded by a later redefinition of the same tag).
     *
     * <p>Field lookups ({@link #resolvedFields()}) are delegated through this reference instead of
     * value-snapshotting the field map at copy time. This matters for self-referential structs
     * (e.g. an intrusive linked list's {@code struct list_head *next;} field): the pointer field's
     * type is a copy created WHILE the enclosing struct is still being parsed, i.e. before its own
     * fields (including possibly `next` itself) have all been added. Snapshotting at that point
     * would freeze an empty (or partial) field map into the copy forever. Delegating instead means
     * the copy always sees the canonical definition's current (eventually complete) field map.
     * Binding to the specific object (rather than re-resolving the tag name through {@link
     * #definedTypes} on every access) also means a later, genuine redefinition of the same tag name
     * does not retroactively change the fields already-created copies resolve to.
     */
    private final Struct canonicalRef;

    private boolean currentlyBeingBuilt;

    /**
     * Set while this tag's `{ ... }` body is being read, i.e. between the first member and the last
     * (see {@link #beginDefinition()}). A tag in that state is just as incomplete as one with no
     * body at all: expanding it yields whatever members have been seen so far, and the rest arrive
     * afterwards. It matters because a member can pull the *enclosing* tag back in mid-definition
     * -- `struct cert_st { ...; RSA *(*cb)(SSL *ssl, int, int); ...; CERT_PKEY pkeys[5]; }`
     * resolves the typedef `SSL` while reading that parameter, and `struct ssl_st` has a `struct
     * cert_st *cert` member, so `cert_st` is expanded (and cached into `ssl_st`) with only its
     * first five members. Without this flag that half-expansion is treated as complete and never
     * invalidated, so `(s->cert)->pkeys` fails with "field not found" for the rest of the run.
     */
    private boolean definitionInProgress;

    /**
     * The expanded field list of the *canonical* definition, shared by every copy. A nested struct
     * type re-expands its whole subtree on each use; without this cache the expansion is
     * exponential in nesting depth (large LDV kernel headers ran out of heap inside it).
     * Invalidated on {@link #addField}, so a still-growing definition never serves a stale
     * snapshot.
     */
    private List<Tuple2<String, CComplexType>> cachedActualFields;

    /**
     * The tags expanded while still field-less during the expansion currently in progress, one set
     * per nesting level (see {@link #getActualType()}). A level's set is merged into its parent's
     * when it finishes, so an enclosing struct learns about incomplete tags found anywhere beneath
     * it, not just among its own immediate members.
     */
    private static final java.util.Deque<java.util.Set<String>> expansionFrames =
            new java.util.ArrayDeque<>();

    /**
     * Tag → the canonical structs whose cached expansion baked in that tag while it was still
     * field-less. {@link #addField} clears exactly these when the tag is finally defined.
     *
     * <p>This exists because {@code addField} invalidating only its *own* cache is not enough: in a
     * CIL-preprocessed kernel source `struct device` expands `struct device_private *p` hundreds of
     * thousands of characters before that tag is defined, so `struct device` keeps a pointer to a
     * field-less struct forever and every `(dev->p)->driver_data` fails with "available fields are:
     * []".
     *
     * <p>Targeted invalidation, rather than the two blunter options, both of which were measured:
     * declining to cache an incomplete expansion at all sounds narrow ("incomplete tags are rare")
     * but is not -- forward declarations are pervasive in these sources, so nearly nothing cached
     * and three LDV files went from ~19s to `OutOfMemoryError`, the expansion being exponential in
     * nesting depth. A global generation counter invalidating every cache per `addField` fails the
     * same way for the whole declaration phase.
     */
    private static final Map<String, java.util.Set<Struct>> incompleteDependents =
            new LinkedHashMap<>();

    /** Unnamed bitfields, in declaration order; see {@link #addPadding}. */
    private final List<CStruct.Padding> paddings = new ArrayList<>();

    /** `packed` / `aligned(n)` on the struct itself; see {@link #setLayoutAttributes}. */
    private ObjectLayout.Attributes layoutAttributes = ObjectLayout.Attributes.NONE;

    private static final Map<String, Struct> definedTypes = new LinkedHashMap<>();

    public static Struct getByName(String name) {
        return getByName(name, false);
    }

    /** `struct X` and `union X` are distinct types, so the tag alone does not identify one. */
    public static Struct getByName(String name, boolean union) {
        return definedTypes.get(tagOf(name, union));
    }

    private static String tagOf(String name, boolean union) {
        return (union ? "union " : "struct ") + name;
    }

    Struct(String name, ParseContext parseContext, Logger uniqueWarningLogger) {
        this(name, false, parseContext, uniqueWarningLogger);
    }

    Struct(String name, boolean union, ParseContext parseContext, Logger uniqueWarningLogger) {
        super(parseContext, union ? "union" : "struct", uniqueWarningLogger);
        this.uniqueWarningLogger = uniqueWarningLogger;
        this.union = union;
        fields = new LinkedHashMap<>();
        this.name = name;
        this.canonicalRef = null;
        if (name != null) {
            definedTypes.put(tagOf(name, union), this);
        }
        currentlyBeingBuilt = false;
    }

    private Struct(Struct from) {
        super(from.parseContext, from.union ? "union" : "struct", from.uniqueWarningLogger);
        fields = new LinkedHashMap<>();
        this.name = from.name;
        this.union = from.union;
        this.uniqueWarningLogger = from.uniqueWarningLogger;
        this.canonicalRef = from.canonical();
        currentlyBeingBuilt = false;
    }

    public boolean isUnion() {
        return union;
    }

    /** The struct definition instance this instance's fields should be resolved from. */
    private Struct canonical() {
        return canonicalRef != null ? canonicalRef : this;
    }

    /**
     * The authoritative, possibly still-growing, field map for this struct (see {@link
     * #canonicalRef}).
     */
    private Map<String, CDeclaration> resolvedFields() {
        return canonical().fields;
    }

    /** Whether this tag has been given a body yet (see the forward-declaration path). */
    public boolean hasFields() {
        return !canonical().fields.isEmpty();
    }

    /**
     * The tag as written (`struct device_private`), for diagnostics. An unresolved member access
     * reports only the field name, which cannot tell "resolved the wrong struct" apart from "right
     * struct, no fields" -- and that distinction is what a field-less struct error hinges on.
     */
    public String getTagName() {
        return (union ? "union " : "struct ") + (name == null ? "<anonymous>" : name);
    }

    /**
     * Mark the start of this tag's member list; see {@link #definitionInProgress}. Paired with
     * {@link #endDefinition()}.
     */
    public void beginDefinition() {
        canonical().definitionInProgress = true;
    }

    /** Mark the member list finished; see {@link #definitionInProgress}. */
    public void endDefinition() {
        canonical().definitionInProgress = false;
    }

    public void addField(CDeclaration decl) {
        fields.put(checkNotNull(decl.getName()), checkNotNull(decl));
        cachedActualFields = null;
        canonical().cachedActualFields = null;
        // Anything that cached an expansion containing this tag while it was still field-less is
        // now stale. The entry is kept rather than removed: fields arrive one at a time, and a
        // dependent could re-cache between two of them.
        if (name != null) {
            final java.util.Set<Struct> dependents = incompleteDependents.get(tagOf(name, union));
            if (dependents != null) {
                for (Struct dependent : dependents) {
                    dependent.cachedActualFields = null;
                }
            }
        }
    }

    /**
     * Record an unnamed bitfield (`int : 3;`, `int : 0;`). It is padding, so it gets no field --
     * but it moves where the next member sits, which {@link CStruct.Padding} preserves. Stored on
     * the canonical definition, like the fields themselves.
     */
    public void addPadding(int bitWidth, int baseBits) {
        final Struct canonical = canonical();
        canonical.paddings.add(new CStruct.Padding(canonical.fields.size(), bitWidth, baseBits));
    }

    /** Layout attributes (`packed`, `aligned(n)`) on the struct itself. */
    public void setLayoutAttributes(ObjectLayout.Attributes attributes) {
        canonical().layoutAttributes = attributes;
    }

    @Override
    public CComplexType getActualType() {
        if (currentlyBeingBuilt) {
            uniqueWarningLogger.write(
                    Level.INFO, "WARNING: self-embedded structs! Using long as a placeholder\n");
            CComplexType placeholder = CComplexType.getSignedInt(parseContext);
            for (int i = 0; i < getPointerLevel(); i++) {
                placeholder = new CPointer(this, placeholder, parseContext);
            }
            return placeholder;
        }
        currentlyBeingBuilt = true;
        final Struct canonical = canonical();
        // Expanding a tag whose body is not (fully) parsed yet yields a CStruct missing members --
        // unavoidable, they have not been read. Report it to the expansion in progress so that
        // whatever caches this result can be invalidated when the remaining members arrive. Both an
        // undefined tag and one whose `{ ... }` is still being read count (see
        // #definitionInProgress).
        if (name != null
                && (canonical.fields.isEmpty() || canonical.definitionInProgress)
                && !expansionFrames.isEmpty()) {
            expansionFrames.peek().add(tagOf(name, union));
        }
        List<Tuple2<String, CComplexType>> actualFields = canonical.cachedActualFields;
        if (actualFields == null) {
            final java.util.Set<String> frame = new java.util.LinkedHashSet<>();
            expansionFrames.push(frame);
            final List<Tuple2<String, CComplexType>> expanded = new ArrayList<>();
            try {
                resolvedFields()
                        .forEach(
                                (s, cDeclaration) ->
                                        expanded.add(Tuple2.of(s, cDeclaration.getActualType())));
            } finally {
                expansionFrames.pop();
            }
            canonical.cachedActualFields = expanded;
            for (String tag : frame) {
                incompleteDependents
                        .computeIfAbsent(tag, k -> new java.util.LinkedHashSet<>())
                        .add(canonical);
            }
            // Ancestors depend on these tags too: their own expansion contains this one.
            if (!expansionFrames.isEmpty()) {
                expansionFrames.peek().addAll(frame);
            }
            actualFields = expanded;
        }
        currentlyBeingBuilt = false;

        // Carry each field's bitfield width (parallel to actualFields) so CStruct can pack
        // consecutive bitfields into shared storage units. resolvedFields() is insertion-ordered,
        // the same order actualFields was built in.
        final List<Integer> bitfieldWidths = new ArrayList<>();
        resolvedFields()
                .forEach((s, cDeclaration) -> bitfieldWidths.add(cDeclaration.getBitfieldWidth()));

        // Layout attributes and unnamed-bitfield padding live on the canonical definition too: a
        // copy is made mid-parse (see canonicalRef) and would otherwise freeze an empty list.
        final List<ObjectLayout.Attributes> fieldAttributes = new ArrayList<>();
        resolvedFields()
                .forEach(
                        (s, cDeclaration) ->
                                fieldAttributes.add(cDeclaration.getLayoutAttributes()));

        CComplexType type =
                new CStruct(
                        this,
                        actualFields,
                        union,
                        parseContext,
                        bitfieldWidths,
                        canonical().paddings,
                        canonical().layoutAttributes,
                        fieldAttributes);
        if (isAtomic()) {
            type.setAtomic();
        }

        for (int i = 0; i < getPointerLevel(); i++) {
            type = new CPointer(this, type, parseContext);
            if (isAtomicPointer(i)) {
                type.setAtomic();
            }
        }

        return type;
    }

    @Override
    public CSimpleType getBaseType() {
        return this;
    }

    @Override
    public boolean isVoid() {
        return false;
    }

    @Override
    public CSimpleType copyOf() {
        var ret = new Struct(this);
        setUpCopy(ret);
        return ret;
    }
}
