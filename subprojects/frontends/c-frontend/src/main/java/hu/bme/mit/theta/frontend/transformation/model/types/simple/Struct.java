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
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public class Struct extends NamedType {

    private final Map<String, CDeclaration> fields;
    private final String name;
    private final Logger uniqueWarningLogger;

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
    private static final Map<String, Struct> definedTypes = new LinkedHashMap<>();

    public static Struct getByName(String name) {
        return definedTypes.get(name);
    }

    Struct(String name, ParseContext parseContext, Logger uniqueWarningLogger) {
        super(parseContext, "struct", uniqueWarningLogger);
        this.uniqueWarningLogger = uniqueWarningLogger;
        fields = new LinkedHashMap<>();
        this.name = name;
        this.canonicalRef = null;
        if (name != null) {
            definedTypes.put(name, this);
        }
        currentlyBeingBuilt = false;
    }

    private Struct(Struct from) {
        super(from.parseContext, "struct", from.uniqueWarningLogger);
        fields = new LinkedHashMap<>();
        this.name = from.name;
        this.uniqueWarningLogger = from.uniqueWarningLogger;
        this.canonicalRef = from.canonical();
        currentlyBeingBuilt = false;
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

    public void addField(CDeclaration decl) {
        fields.put(checkNotNull(decl.getName()), checkNotNull(decl));
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
        List<Tuple2<String, CComplexType>> actualFields = new ArrayList<>();
        resolvedFields()
                .forEach(
                        (s, cDeclaration) ->
                                actualFields.add(Tuple2.of(s, cDeclaration.getActualType())));
        currentlyBeingBuilt = false;

        CComplexType type = new CStruct(this, actualFields, parseContext);

        for (int i = 0; i < getPointerLevel(); i++) {
            type = new CPointer(this, type, parseContext);
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
