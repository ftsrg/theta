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
package hu.bme.mit.theta.frontend.transformation.model.types.complex.compound;

import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clong.CUnsignedLong;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;
import java.util.Objects;
import java.util.function.Supplier;

public class CPointer extends CInteger {

    private final CComplexType embeddedType;

    /**
     * Non-null for a pointer created by {@link #resolvedOnAccess}; then it replaces embeddedType.
     */
    private final Supplier<CComplexType> embeddedTypeResolver;

    /**
     * True when this pointer holds a function's address (id) rather than a data-object address, so
     * that a call through it is dispatched over the candidate set. Carried on the TYPE (not just on
     * a variable) so that function pointers stored in struct fields, arrays and typedefs are
     * recognized too.
     */
    private boolean functionPointer = false;

    public boolean isFunctionPointer() {
        return functionPointer;
    }

    public void setFunctionPointer(boolean functionPointer) {
        this.functionPointer = functionPointer;
    }

    public CPointer(CSimpleType origin, CComplexType embeddedType, ParseContext parseContext) {
        super(origin, parseContext);
        this.embeddedType = embeddedType;
        this.embeddedTypeResolver = null;
    }

    private CPointer(
            CSimpleType origin, ParseContext parseContext, Supplier<CComplexType> resolver) {
        super(origin, parseContext);
        this.embeddedType = null;
        this.embeddedTypeResolver = resolver;
    }

    /**
     * A pointer whose pointee is computed on every access instead of being fixed now. A recursive
     * struct's pointer to itself needs this: an eagerly built pointee would have to contain the
     * struct that is still being expanded, so the type tree would be cut off at some depth.
     */
    public static CPointer resolvedOnAccess(
            CSimpleType origin, Supplier<CComplexType> embeddedType, ParseContext parseContext) {
        return new CPointer(origin, parseContext, embeddedType);
    }

    public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
        return visitor.visit(this, param);
    }

    @Override
    public CInteger getSignedVersion() {
        return this;
    }

    @Override
    public CInteger getUnsignedVersion() {
        return this;
    }

    public CComplexType getEmbeddedType() {
        return embeddedTypeResolver != null ? embeddedTypeResolver.get() : embeddedType;
    }

    @Override
    public String getTypeName() {
        return new CUnsignedLong(null, parseContext).getTypeName();
    }

    @Override
    public boolean equals(Object o) {
        if (o == null || getClass() != o.getClass()) return false;
        CPointer cPointer = (CPointer) o;
        // Finite even for a recursive struct: CStruct compares only its members' classes.
        return Objects.equals(getEmbeddedType(), cPointer.getEmbeddedType());
    }

    @Override
    public int hashCode() {
        return Objects.hash(getClass(), getEmbeddedType());
    }
}
