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
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import java.util.ArrayList;
import java.util.List;

/**
 * The byte-exact layout of a C object: where each member starts, and how much room the whole thing
 * takes. This is the AD7 foundation -- the model in which a union member and its sibling name the
 * same bits, and a `char[16]` view of a struct sees that struct's bytes.
 *
 * <p>It is deliberately <b>pure</b>: a function from a {@link CComplexType} and an architecture to
 * offsets. It computes layout; it does not decide how a program addresses it. Nothing in the
 * frontend calls it yet -- wiring it into member access is the separate, riskier half of AD7, and
 * keeping the arithmetic independently testable is what makes that half checkable.
 *
 * <p>Everything is in <b>bits</b>, because bitfields have no byte-granular position. Sizes and
 * alignments of whole objects are still byte multiples, as C requires.
 *
 * <h2>What it implements</h2>
 *
 * The System V rules every target in the benchmark set follows: a member starts at the next offset
 * that satisfies its alignment, a struct's alignment is its strictest member's, a struct's size is
 * rounded up to that alignment (so arrays of it stay aligned), and a union's members all start at
 * zero. Bitfields pack into storage units of their declared base type and a zero-width bitfield
 * closes the current unit.
 *
 * <h2>Layout attributes</h2>
 *
 * {@code __attribute__((packed))} and {@code ((aligned(n)))} change layout, and both are honored:
 * packed drops every member to byte alignment and removes tail padding, {@code aligned(n)} raises
 * an object's or a member's alignment. A member's own {@code aligned(n)} wins over its struct's
 * {@code packed}, which is what GCC does. They reach here through {@link CStruct}, which the
 * {@code TypeVisitor} now populates from the attribute lists the grammar was already parsing (and
 * previously discarded).
 *
 * <h2>Unnamed bitfields</h2>
 *
 * An unnamed bitfield ({@code int : 3;}, {@code int : 0;}) holds no value, so it gets no field --
 * nothing can name it, and giving it a storage cell would shift every following member in the wired
 * cell model. It does move where the next member sits, though, so {@link CStruct.Padding} records
 * it separately and the walk below replays it in declaration order. {@code int : 0;} closes the
 * current storage unit, which is the whole reason the idiom exists.
 */
public final class ObjectLayout {

    /** GCC layout attributes on a declaration. Nothing populates these yet -- see the class note. */
    public record Attributes(boolean packed, int alignedToBits) {
        public static final Attributes NONE = new Attributes(false, 0);
    }

    /**
     * One member's placement. {@code bitfieldWidth} is -1 for an ordinary member; for a bitfield it
     * is the declared width, which is what makes {@code bitOffset} not byte-aligned.
     */
    public record Field(String name, CComplexType type, int bitOffset, int bitWidth, int bitfieldWidth) {
        public boolean isBitfield() {
            return bitfieldWidth >= 0;
        }
    }

    /** A laid-out object: its total size, its alignment, and where its members sit. */
    public record Layout(int bitSize, int bitAlignment, List<Field> fields) {
        /** The placement of [name], or null if this object has no such member. */
        public Field field(String name) {
            for (Field f : fields) {
                if (f.name().equals(name)) {
                    return f;
                }
            }
            return null;
        }
    }

    private ObjectLayout() {}

    /** The layout of [type] under [arch], using whatever attributes the type itself carries. */
    public static Layout of(CComplexType type, ArchitectureType arch) {
        return of(type, arch, type instanceof CStruct s ? s.getAttributes() : Attributes.NONE);
    }

    public static Layout of(CComplexType type, ArchitectureType arch, Attributes attributes) {
        if (type instanceof CStruct struct) {
            return struct.isUnion()
                    ? unionLayout(struct, arch, attributes)
                    : structLayout(struct, arch, attributes);
        }
        // A non-aggregate is its own single field-less object.
        final int size = sizeBits(type, arch);
        return new Layout(size, alignBits(type, arch, attributes), List.of());
    }

    /** The number of bits [type] occupies, padding included. */
    public static int sizeBits(CComplexType type, ArchitectureType arch) {
        if (type instanceof CStruct struct) {
            return of(struct, arch).bitSize();
        }
        if (type instanceof CArray array) {
            final Integer count = constantDimension(array);
            if (count == null) {
                // A flexible array member (`int a[];`) contributes nothing to its struct's size, and
                // a VLA has no static size at all. Both are "no bits here" for layout purposes.
                return 0;
            }
            return count * sizeBits(array.getEmbeddedType(), arch);
        }
        // Pointers report the width of `unsigned long`, which is the pointer width in both ILP32
        // and LP64 -- the two models this frontend supports.
        return type.width();
    }

    /**
     * The alignment [type] demands, in bits.
     *
     * <p>A scalar aligns to its own size, capped by the architecture's widest scalar alignment: the
     * i386 quirk that an 8-byte {@code long long} or {@code double} aligns to 4 is exactly this cap.
     * Types at least 128 bits wide ({@code long double}, {@code __int128}) align to their size on
     * LP64 instead, which is what the x86-64 psABI specifies.
     */
    public static int alignBits(CComplexType type, ArchitectureType arch, Attributes attributes) {
        if (attributes.alignedToBits() > 0) {
            return attributes.alignedToBits();
        }
        if (attributes.packed()) {
            return 8;
        }
        if (type instanceof CStruct struct) {
            return of(struct, arch).bitAlignment();
        }
        if (type instanceof CArray array) {
            // An array is as aligned as one element.
            return alignBits(array.getEmbeddedType(), arch, Attributes.NONE);
        }
        final int size = type.width();
        final int cap = arch == ArchitectureType.LP64 ? 64 : 32;
        if (size >= 128 && arch == ArchitectureType.LP64) {
            return size;
        }
        return Math.min(size, cap);
    }

    private static Layout structLayout(
            CStruct struct, ArchitectureType arch, Attributes attributes) {
        final List<Field> fields = new ArrayList<>();
        final List<Tuple2<String, CComplexType>> members = struct.getFields();
        int offset = 0;
        int alignment = 8; // a struct is at least byte-aligned
        for (int i = 0; i <= members.size(); i++) {
            // Unnamed bitfields hold no value but do move the next member, so they are replayed
            // here in declaration order even though they have no field of their own.
            for (CStruct.Padding padding : struct.getPaddings()) {
                if (padding.afterFieldIndex() != i) {
                    continue;
                }
                final int unitBits = padding.baseBits();
                if (padding.bitWidth() == 0) {
                    // `int : 0;` closes the current storage unit: the next member starts fresh.
                    offset = roundUp(offset, attributes.packed() ? 8 : unitBits);
                } else {
                    if (!attributes.packed() && offset % unitBits + padding.bitWidth() > unitBits) {
                        offset = roundUp(offset, unitBits);
                    }
                    offset += padding.bitWidth();
                    // No alignment contribution: gcc gives `struct {char a; int :3; char b;}`
                    // alignment 1, not 4. An unnamed bitfield reserves bits without making the
                    // struct as strict as the type it borrowed them from. (A *named* bitfield does
                    // contribute -- `struct {unsigned a:4;}` is 4-aligned.)
                }
            }
            if (i == members.size()) {
                break; // the extra pass exists only to replay trailing padding
            }
            final CComplexType memberType = members.get(i).get2();
            final Attributes memberAttributes = struct.fieldAttributes(i);
            final int bitfieldWidth = struct.declaredBitfieldWidth(i);
            if (bitfieldWidth >= 0) {
                final int unitBits = memberType.width();
                if (bitfieldWidth == 0) {
                    offset = roundUp(offset, attributes.packed() ? 8 : unitBits);
                    continue;
                }
                if (!attributes.packed() && offset % unitBits + bitfieldWidth > unitBits) {
                    // It would straddle a storage unit, so it starts a new one instead.
                    offset = roundUp(offset, unitBits);
                }
                fields.add(
                        new Field(
                                members.get(i).get1(),
                                memberType,
                                offset,
                                bitfieldWidth,
                                bitfieldWidth));
                offset += bitfieldWidth;
                alignment = Math.max(alignment, attributes.packed() ? 8 : unitBits);
                continue;
            }
            // A member's own `aligned(n)` raises its alignment even inside a packed struct; a
            // packed struct otherwise drops every member to byte alignment.
            final int memberAlign =
                    memberAttributes.alignedToBits() > 0
                            ? memberAttributes.alignedToBits()
                            : (attributes.packed() || memberAttributes.packed()
                                    ? 8
                                    : alignBits(memberType, arch, Attributes.NONE));
            offset = roundUp(offset, memberAlign);
            final int size = sizeBits(memberType, arch);
            fields.add(new Field(members.get(i).get1(), memberType, offset, size, -1));
            offset += size;
            alignment = Math.max(alignment, memberAlign);
        }
        if (attributes.alignedToBits() > 0) {
            alignment = Math.max(alignment, attributes.alignedToBits());
        }
        // Tail padding: sizeof must be a multiple of the alignment, or an array of this struct
        // would misalign its second element.
        return new Layout(roundUp(offset, alignment), alignment, fields);
    }

    private static Layout unionLayout(CStruct union, ArchitectureType arch, Attributes attributes) {
        final List<Field> fields = new ArrayList<>();
        int size = 0;
        int alignment = 8;
        final List<Tuple2<String, CComplexType>> members = union.getFields();
        for (int i = 0; i < members.size(); i++) {
            final CComplexType memberType = members.get(i).get2();
            final int bitfieldWidth = union.declaredBitfieldWidth(i);
            final int memberBits =
                    bitfieldWidth >= 0 ? bitfieldWidth : sizeBits(memberType, arch);
            // Every union member starts at the same address -- that is the whole construct.
            fields.add(new Field(members.get(i).get1(), memberType, 0, memberBits, bitfieldWidth));
            size = Math.max(size, memberBits);
            alignment =
                    Math.max(
                            alignment,
                            attributes.packed() ? 8 : alignBits(memberType, arch, Attributes.NONE));
        }
        if (attributes.alignedToBits() > 0) {
            alignment = Math.max(alignment, attributes.alignedToBits());
        }
        return new Layout(roundUp(size, alignment), alignment, fields);
    }

    /** The element count of a fixed-size array, or null when it has none (flexible member, VLA). */
    public static Integer constantDimension(CArray array) {
        if (array.getArrayDimension() == null) {
            return null;
        }
        final var folded = ExprUtils.simplify(array.getArrayDimension().getExpression());
        if (folded instanceof IntLitExpr intLit) {
            return intLit.getValue().intValueExact();
        }
        if (folded instanceof BvLitExpr bvLit) {
            return BvUtils.neutralBvLitExprToBigInteger(bvLit).intValueExact();
        }
        return null;
    }

    private static int roundUp(int value, int multiple) {
        if (multiple <= 0) {
            return value;
        }
        final int remainder = value % multiple;
        return remainder == 0 ? value : value + multiple - remainder;
    }
}
