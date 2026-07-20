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

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clong.CUnsignedLong;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;
import java.util.stream.Collectors;

public class CStruct extends CInteger {

    /**
     * Field-list name given to a C11 anonymous struct/union member. Member lookup flattens
     * through fields with this prefix, so `s.a` finds `a` inside `struct S { union { int a; }; }`.
     */
    public static final String ANONYMOUS_FIELD_PREFIX = "__theta_anon_";

    private final List<Tuple2<String, CComplexType>> fields;
    private final boolean union;

    /**
     * Per-field storage-unit layout, parallel to {@link #fields}. For a struct with no bitfields
     * every field is its own unit and {@code slots.get(i).unitIndex() == i} -- byte-for-byte the
     * historical one-cell-per-field model. Consecutive bitfields pack into a shared unit (see
     * {@link BitfieldLayout}), so a member access lowers to that unit's cell and, for a bitfield,
     * a slice of it.
     */
    private final List<BitfieldLayout.Slot> slots;

    private final int unitCount;

    public CStruct(
            CSimpleType origin,
            List<Tuple2<String, CComplexType>> fields,
            ParseContext parseContext) {
        this(origin, fields, false, parseContext);
    }

    public CStruct(
            CSimpleType origin,
            List<Tuple2<String, CComplexType>> fields,
            boolean union,
            ParseContext parseContext) {
        this(origin, fields, union, parseContext, allOrdinary(fields.size()));
    }

    /**
     * @param bitfieldWidths bitfield width per field (-1 for an ordinary, non-bitfield member),
     *     parallel to {@code fields}. Only meaningful for structs; a union's members all share
     *     offset 0 regardless (see {@link #isUnion()}), so its layout is not consulted.
     */
    public CStruct(
            CSimpleType origin,
            List<Tuple2<String, CComplexType>> fields,
            boolean union,
            ParseContext parseContext,
            List<Integer> bitfieldWidths) {
        super(origin, parseContext);
        this.fields = fields;
        this.union = union;
        final List<BitfieldLayout.Member> members = new java.util.ArrayList<>(fields.size());
        for (int i = 0; i < fields.size(); i++) {
            final int bitfieldWidth = i < bitfieldWidths.size() ? bitfieldWidths.get(i) : -1;
            // The base-type width only matters for a bitfield (its unit's packing capacity); for an
            // ordinary member it is unused, so avoid width() -- which throws for aggregate members.
            final int baseBits = bitfieldWidth >= 0 ? fields.get(i).get2().width() : 0;
            members.add(new BitfieldLayout.Member(baseBits, bitfieldWidth));
        }
        final BitfieldLayout.Layout layout = BitfieldLayout.compute(members);
        this.slots = layout.slots();
        this.unitCount = layout.unitCount();
    }

    private static List<Integer> allOrdinary(int n) {
        final List<Integer> widths = new java.util.ArrayList<>(n);
        for (int i = 0; i < n; i++) {
            widths.add(-1);
        }
        return widths;
    }

    /** The number of storage cells the struct occupies (units, not members). */
    public int getUnitCount() {
        return union ? 1 : unitCount;
    }

    /**
     * Whether the whole struct is one packed integer: a single storage unit made up entirely of
     * bitfields. Such a struct has no substructure to address -- its content *is* the unit's value
     * -- so as a union member it can share the union's cell with a sibling integer of the same
     * width, which is exactly the {@code union { uint64_t raw; struct { uint64_t a:16; ... }; }}
     * register-overlay idiom. Its members are then slices of that shared cell.
     */
    public boolean isPackedScalar() {
        return !union
                && unitCount == 1
                && !slots.isEmpty()
                && slots.stream().allMatch(BitfieldLayout.Slot::bitfield);
    }

    /** For a {@link #isPackedScalar()} struct, the integer type its single unit is stored as. */
    public CComplexType packedScalarType() {
        return fields.get(0).get2();
    }

    /** The storage cell index for [memberName], or -1 if it has no field. */
    public int unitOffsetOf(String memberName) {
        final int i = fieldIndexOf(memberName);
        return i < 0 ? -1 : slots.get(i).unitIndex();
    }

    /** The full slice descriptor for [memberName] (unit, bit offset, width, bitfield?), or null. */
    public BitfieldLayout.Slot slotOf(String memberName) {
        final int i = fieldIndexOf(memberName);
        return i < 0 ? null : slots.get(i);
    }

    private int fieldIndexOf(String memberName) {
        for (int i = 0; i < fields.size(); i++) {
            if (fields.get(i).get1().equals(memberName)) {
                return i;
            }
        }
        return -1;
    }

    /**
     * A union's members all start at the same address, so they are all given member offset 0. Since
     * a member access lowers to `__arrays_T[base][offset]` -- an array *per SMT type* -- two
     * members of the same type then genuinely alias (writing one is read back by the other, which
     * is the whole point of the construct), while members of different types land in different
     * arrays and cannot alias at all. Bit-exact punning across differently-typed members needs the
     * flat object layout of AD7 and is rejected rather than answered unsoundly.
     */
    public boolean isUnion() {
        return union;
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

    public Map<String, CComplexType> getFieldsAsMap() {
        return fields.stream().collect(Collectors.toMap(Tuple2::get1, Tuple2::get2));
    }

    public List<Tuple2<String, CComplexType>> getFields() {
        return fields;
    }

    @Override
    public String getTypeName() {
        return new CUnsignedLong(null, parseContext).getTypeName();
    }

    @Override
    public boolean equals(Object o) {
        if (o == null || getClass() != o.getClass()) return false;
        CStruct cStruct = (CStruct) o;
        final Function<Tuple2<String, CComplexType>, Tuple2<String, Class<?>>> mapper =
                (Tuple2<String, CComplexType> it) -> Tuple2.of(it.get1(), it.get2().getClass());
        return Objects.equals(
                fields.stream().map(mapper).toList(), cStruct.fields.stream().map(mapper).toList());
    }

    @Override
    public int hashCode() {
        final Function<Tuple2<String, CComplexType>, Tuple2<String, Class<?>>> mapper =
                (Tuple2<String, CComplexType> it) -> Tuple2.of(it.get1(), it.get2().getClass());
        return Objects.hash(getClass(), fields.stream().map(mapper).toList());
    }
}
