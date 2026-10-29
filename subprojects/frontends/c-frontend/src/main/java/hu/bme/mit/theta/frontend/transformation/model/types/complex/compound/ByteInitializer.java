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
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType;
import hu.bme.mit.theta.frontend.transformation.grammar.expression.UnsupportedInitializer;
import hu.bme.mit.theta.frontend.transformation.model.statements.CExpr;
import hu.bme.mit.theta.frontend.transformation.model.statements.CInitializerList;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar.CUnsignedChar;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * Where an object's initializer lands under the bytes memory model, in which every member and
 * element sits at its real {@link ObjectLayout} byte offset of the one object. The global and the
 * stack initializers both use it, so they write the bytes the accesses read.
 *
 * <p>Brace elision follows C17 6.7.9p20: a scalar where an aggregate is expected starts filling
 * that aggregate's leaves from the enclosing list, and a designator ends the elided run.
 */
public final class ByteInitializer {

    /**
     * A value stored at {@code byteOffset} as {@code type}. For a bitfield, {@code type} is the
     * storage unit's declared type, and the value goes into its {@code [bitInUnit, +width)} bits.
     */
    public record Leaf(
            int byteOffset, CComplexType type, CStatement value, int bitInUnit, int width) {
        public boolean isBitfield() {
            return width >= 0;
        }
    }

    /** A cell of the object, as the zero-initialization writes it. */
    public record Cell(int byteOffset, CComplexType type) {}

    private final ParseContext parseContext;
    private final ArchitectureType arch;

    public ByteInitializer(ParseContext parseContext) {
        this.parseContext = parseContext;
        this.arch = parseContext.getArchitecture();
    }

    /** The values [init] stores into an object of [type], in initializer order. */
    public List<Leaf> leaves(CComplexType type, CStatement init) {
        final List<Leaf> out = new ArrayList<>();
        if (init instanceof CInitializerList list) {
            fill(type, 0, new Entries(list), true, out);
        } else if (init != null) {
            final CInitializerList single = new CInitializerList(type, parseContext);
            single.addStatement(null, init);
            place(type, 0, null, new Entries(single), out);
        }
        out.removeIf(
                leaf ->
                        leaf.value() instanceof CExpr e
                                && e.getExpression() instanceof UnsupportedInitializer);
        return out;
    }

    /**
     * The cells zero-initialization writes: every scalar at its offset, every bitfield storage unit
     * once, and a union byte by byte, since its members overlap. [count] overrides the element
     * count of an array that takes its extent from the initializer.
     */
    public List<Cell> cells(CComplexType type, Integer count) {
        final List<Cell> out = new ArrayList<>();
        zero(type, 0, count, new LinkedHashSet<>(), out);
        return out;
    }

    /** How many elements [init] gives an array whose declaration leaves the extent to it. */
    public static int elementCount(CStatement init) {
        if (!(init instanceof CInitializerList list)) {
            return 1;
        }
        int next = 0;
        int elements = 0;
        final List<Tuple2<Optional<CStatement>, CStatement>> statements = list.getStatements();
        for (int i = 0; i < statements.size(); i++) {
            final Integer designated = list.isDesignated(i) ? designator(statements.get(i)) : null;
            next = (designated == null ? next : designated) + 1;
            elements = Math.max(elements, next);
        }
        return elements;
    }

    private void zero(
            CComplexType type, int offset, Integer count, Set<Integer> units, List<Cell> out) {
        if (type instanceof CArray array) {
            final Integer dimension = count != null ? count : ObjectLayout.constantDimension(array);
            if (dimension == null) {
                return;
            }
            final CComplexType element = array.getEmbeddedType();
            final int stride = bytes(element);
            for (int i = 0; i < dimension; i++) {
                zero(element, offset + i * stride, null, units, out);
            }
        } else if (type instanceof CStruct struct && struct.isUnion()) {
            final CComplexType byteType = new CUnsignedChar(null, parseContext);
            for (int i = 0; i < bytes(struct); i++) {
                out.add(new Cell(offset + i, byteType));
            }
        } else if (type instanceof CStruct struct) {
            for (ObjectLayout.Field field : ObjectLayout.of(struct, arch).fields()) {
                if (field.isBitfield()) {
                    final int unit = offset + unitByteOffset(field);
                    if (units.add(unit)) {
                        out.add(new Cell(unit, field.type()));
                    }
                } else {
                    zero(field.type(), offset + field.bitOffset() / 8, null, units, out);
                }
            }
        } else {
            out.add(new Cell(offset, type));
        }
    }

    /**
     * Fills [type] at [offset] from [entries]: all of them when [braced], else (an elided
     * aggregate) only as many as its leaves take, stopping at the next designator.
     */
    private void fill(
            CComplexType type, int offset, Entries entries, boolean braced, List<Leaf> out) {
        if (type instanceof CArray array) {
            final Integer dimension = ObjectLayout.constantDimension(array);
            final CComplexType element = array.getEmbeddedType();
            final int stride = bytes(element);
            int index = 0;
            boolean first = true;
            while (entries.hasNext()) {
                final Integer designated = entries.designator();
                if (designated != null && !first && !braced) {
                    return;
                }
                if (designated != null && (braced || !first)) {
                    index = designated;
                }
                if (dimension != null && index >= dimension) {
                    if (!braced) {
                        return;
                    }
                    entries.take(); // excess initializer: a constraint violation, ignored
                    continue;
                }
                place(element, offset + index * stride, null, entries, out);
                index++;
                first = false;
            }
        } else if (type instanceof CStruct struct) {
            final List<Tuple2<String, CComplexType>> fields = struct.getFields();
            final ObjectLayout.Layout layout = ObjectLayout.of(struct, arch);
            final int limit = struct.isUnion() ? Math.min(1, fields.size()) : fields.size();
            int index = 0;
            int placed = 0;
            boolean first = true;
            while (entries.hasNext()) {
                final Integer designated = entries.designator();
                if (designated != null && !first && !braced) {
                    return;
                }
                if (designated != null && (braced || !first)) {
                    index = designated;
                }
                // A union takes one member; the rest of a braced list is excess.
                if (index >= fields.size() || (struct.isUnion() && placed >= limit)) {
                    if (!braced) {
                        return;
                    }
                    entries.take();
                    continue;
                }
                final ObjectLayout.Field field = layout.field(fields.get(index).get1());
                if (field == null) {
                    throw new UnsupportedFrontendElementException(
                            "Member [%s] of a byte-addressed struct has no resolved layout."
                                    .formatted(fields.get(index).get1()));
                }
                place(field.type(), offset + field.bitOffset() / 8, field, entries, out);
                index++;
                placed++;
                first = false;
            }
        } else if (entries.hasNext()) {
            place(type, offset, null, entries, out); // a braced scalar, `int x = {5}`
            while (braced && entries.hasNext()) {
                entries.take();
            }
        }
    }

    /** Stores the next entry (or, by brace elision, the next run of entries) into [type]. */
    private void place(
            CComplexType type,
            int offset,
            ObjectLayout.Field field,
            Entries entries,
            List<Leaf> out) {
        final int before = entries.position;
        final CStatement value = entries.peek().get2();
        if (value instanceof CInitializerList nested) {
            entries.take();
            fill(type, offset, new Entries(nested), true, out);
        } else if (isAggregate(type) && !isAggregateValue(value)) {
            fill(type, offset, entries, false, out);
        } else {
            entries.take();
            if (field != null && field.isBitfield()) {
                final int unit = unitByteOffset(field);
                out.add(
                        new Leaf(
                                offset - field.bitOffset() / 8 + unit,
                                field.type(),
                                value,
                                field.bitOffset() - unit * 8,
                                field.bitfieldWidth()));
            } else {
                out.add(new Leaf(offset, type, value, -1, -1));
            }
        }
        if (entries.position == before) {
            entries.take(); // nothing to fill (an empty aggregate): drop the entry
        }
    }

    /**
     * The byte offset, within its struct, of the storage unit a bitfield is read from -- the same
     * unit {@code ExpressionVisitor#byteModeBitfieldAccess} slices.
     */
    private static int unitByteOffset(ObjectLayout.Field field) {
        final int unitBits = field.type().width();
        final int unit = (field.bitOffset() / unitBits) * (unitBits / 8);
        if (field.bitOffset() - unit * 8 + field.bitfieldWidth() > unitBits) {
            throw new UnsupportedFrontendElementException(
                    "Bitfield member [%s] straddles two storage units, which the bytes memory model"
                                    .formatted(field.name())
                            + " does not support.");
        }
        return unit;
    }

    private int bytes(CComplexType type) {
        return ObjectLayout.sizeBits(type, arch) / 8;
    }

    private static boolean isAggregate(CComplexType type) {
        return type instanceof CArray || type instanceof CStruct;
    }

    /** Whether [value] is a whole aggregate (a struct copy), not a scalar to elide braces for. */
    private boolean isAggregateValue(CStatement value) {
        return (value instanceof CExpr
                        || value
                                instanceof
                                hu.bme.mit.theta.frontend.transformation.model.statements.CCompound)
                && isAggregate(CComplexType.getType(value.getExpression(), parseContext));
    }

    private static Integer designator(Tuple2<Optional<CStatement>, CStatement> entry) {
        return entry.get1()
                .map(d -> ((IntLitExpr) d.getExpression()).getValue().intValueExact())
                .orElse(null);
    }

    /** A cursor over an initializer list, shared with the elided sub-aggregates it fills. */
    private static final class Entries {
        private final CInitializerList list;
        private final List<Tuple2<Optional<CStatement>, CStatement>> statements;
        private int position;

        Entries(CInitializerList list) {
            this.list = list;
            this.statements = list.getStatements();
        }

        /** The position the next entry's designator names, or null when it has none. */
        Integer designator() {
            return list.isDesignated(position) ? ByteInitializer.designator(peek()) : null;
        }

        boolean hasNext() {
            return position < statements.size();
        }

        Tuple2<Optional<CStatement>, CStatement> peek() {
            return statements.get(position);
        }

        void take() {
            position++;
        }
    }
}
