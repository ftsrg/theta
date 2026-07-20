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

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Div;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mod;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mul;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Sub;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

/**
 * Read and write a bitfield that lives as a slice of a shared storage-unit cell (see {@link
 * BitfieldLayout}). The cell is one packed integer; a member {@code b:w} at bit offset {@code o} is
 * the {@code w}-bit field starting there. Works for both arithmetic encodings: a bitvector cell
 * uses {@code Extract}/{@code Concat} (inherently logical), an integer cell uses the equivalent
 * {@code / 2^o mod 2^w} / place-and-recombine arithmetic.
 */
public final class BitfieldSlice {

    /**
     * Metadata stamped on a bitfield member's *read* expression, naming the cell it was sliced out
     * of. An assignment whose left-hand side carries this must not overwrite the whole cell: it
     * read-modify-writes just the field's bits (see {@link #write}).
     */
    public static final String CELL = "bitfieldCell";

    /** Metadata: the field's bit offset within its cell. */
    public static final String OFFSET = "bitfieldOffset";

    /** Metadata: the field's width in bits. */
    public static final String WIDTH = "bitfieldWidth";

    private BitfieldSlice() {}

    /**
     * The value of the {@code width}-bit field at {@code bitOffset} within {@code cell}, in the
     * cell's own type. Unsigned fields zero-extend; signed fields sign-extend from the field width.
     */
    public static Expr<?> read(Expr<?> cell, int bitOffset, int width, boolean signed) {
        final Type type = cell.getType();
        if (type instanceof BvType bv) {
            final Expr<BvType> slice =
                    BvExprs.Extract(cast(cell, bv), Int(bitOffset), Int(bitOffset + width));
            final BvType full = BvType.of(bv.getSize());
            return signed ? BvExprs.SExt(slice, full) : BvExprs.ZExt(slice, full);
        }
        if (type instanceof IntType) {
            final Expr<IntType> c = cast(cell, IntType.getInstance());
            final Expr<?> unsignedValue = Mod(Div(c, pow2(bitOffset)), pow2(width));
            if (!signed) {
                return unsignedValue;
            }
            // Two's-complement sign: a value with the field's top bit set is negative.
            return Ite(
                    Geq(unsignedValue, pow2(width - 1)), Sub(unsignedValue, pow2(width)), unsignedValue);
        }
        throw new IllegalArgumentException("Unsupported cell type for a bitfield: " + type);
    }

    /**
     * The new value of {@code cell} after storing {@code value}'s low {@code width} bits into the
     * field at {@code bitOffset}, leaving the other bits untouched. {@code value} must already be
     * the cell's type (the assignment casts the right-hand side to the member's base type).
     */
    public static Expr<?> write(Expr<?> cell, Expr<?> value, int bitOffset, int width) {
        final Type type = cell.getType();
        if (type instanceof BvType bv) {
            final int n = bv.getSize();
            final Expr<BvType> c = cast(cell, bv);
            final Expr<BvType> field = BvExprs.Extract(cast(value, bv), Int(0), Int(width));
            // Concat puts its first operand in the high bits: [ bits above the field | field | bits
            // below it ]. Empty ends (offset 0, or field reaching the top) are dropped.
            final List<Expr<BvType>> parts = new ArrayList<>();
            if (bitOffset + width < n) {
                parts.add(BvExprs.Extract(c, Int(bitOffset + width), Int(n)));
            }
            parts.add(field);
            if (bitOffset > 0) {
                parts.add(BvExprs.Extract(c, Int(0), Int(bitOffset)));
            }
            return parts.size() == 1 ? parts.get(0) : BvExprs.Concat(parts);
        }
        if (type instanceof IntType) {
            final Expr<IntType> c = cast(cell, IntType.getInstance());
            final Expr<IntType> v = cast(value, IntType.getInstance());
            final Expr<?> below = Mod(c, pow2(bitOffset)); // bits below the field, kept
            final Expr<?> newField = Mul(Mod(v, pow2(width)), pow2(bitOffset));
            final Expr<?> above =
                    Mul(Div(c, pow2(bitOffset + width)), pow2(bitOffset + width)); // bits above, kept
            return Add(below, Add(newField, above));
        }
        throw new IllegalArgumentException("Unsupported cell type for a bitfield: " + type);
    }

    private static Expr<IntType> pow2(int exponent) {
        return Int(BigInteger.ONE.shiftLeft(exponent));
    }
}
