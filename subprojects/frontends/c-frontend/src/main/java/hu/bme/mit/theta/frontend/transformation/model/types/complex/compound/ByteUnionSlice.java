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

import hu.bme.mit.theta.core.type.BvSignChangeExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

/**
 * Read and write a union member that is laid out as consecutive one-byte cells rather than sharing
 * one packed word (see {@code CStruct#unionCellWidth}). This is AD7's intractable half: a union
 * with an array member -- or one too wide for a word, up to the 4 KB page tables in
 * intel-tdx-module -- has no single cell for a sibling member to slice, so instead each member is
 * the little-endian recombination of the one-byte cells at its own byte offset: {@code
 * Concat(cell[n-1],...,cell[0])} under bitvector, {@code sum cell[j] * 256^j} under integer. Both
 * encodings work because the recombination is always by constant powers of 256, never a variable
 * shift -- unlike a bit-sliced word, which would need {@code 2^(8*i)} for a variable byte index and
 * so only works under bitvector.
 *
 * <p>Like a bitfield read, the <em>value</em> a read produces records where it came from (see
 * {@link StorageOrigin}), so that an assignment through it can find what to write back to: a
 * resolved member value, or an array- or struct-typed member not yet subscripted or accessed.
 */
public final class ByteUnionSlice {

    private ByteUnionSlice() {}

    /**
     * The value of an {@code n}-byte little-endian member from its one-byte cells, {@code
     * cellsLsbFirst.get(0)} being the lowest address (the least-significant byte) -- exactly how
     * {@code u.dwords[i]} sits at bytes {@code [i*4, i*4+4)} with byte {@code i*4} holding the low
     * 8 bits. A signed read reinterprets the top bit of the whole {@code 8*n}-bit member; unsigned
     * needs nothing extra, since every cell is already non-negative.
     */
    public static Expr<?> read(List<Expr<?>> cellsLsbFirst, boolean signed) {
        final Type cellType = cellsLsbFirst.get(0).getType();
        final int n = cellsLsbFirst.size();
        if (cellType instanceof BvType) {
            final List<Expr<BvType>> parts = new ArrayList<>(n);
            for (int j = n - 1; j >= 0; j--) {
                parts.add(cast(cellsLsbFirst.get(j), BvType.of(8)));
            }
            final Expr<BvType> concat = parts.size() == 1 ? parts.get(0) : BvExprs.Concat(parts);
            // Concat yields a *neutral* (signedness-less) bitvector. Stamp it with the member's
            // declared signedness so a relational comparison on the result (`u.x <= n`) is well
            // typed -- Lt/Leq/Gt/Geq reject a neutral BvType. Equality tolerated the neutral type,
            // which is why this only surfaced once a byte-union member reached a `<`/`<=` (the
            // Intel
            // TDX-Module tasks, under bitvector arithmetic).
            return BvSignChangeExpr.of(concat, BvType.of(8 * n, signed));
        }
        if (cellType instanceof IntType) {
            Expr<?> sum = Int(0);
            for (int j = 0; j < n; j++) {
                sum = Add(sum, Mul(cast(cellsLsbFirst.get(j), IntType.getInstance()), pow2(8 * j)));
            }
            if (!signed) {
                return sum;
            }
            final int width = 8 * n;
            return Ite(Geq(sum, pow2(width - 1)), Sub(sum, pow2(width)), sum);
        }
        throw new IllegalArgumentException(
                "Unsupported cell type for a byte-laid-out union: " + cellType);
    }

    /**
     * Splits {@code value} -- already cast to the member's own {@code 8*n}-bit-wide type -- into
     * its {@code n} one-byte cells, {@code [0]} being the lowest address (the least-significant
     * byte). No read-modify-write is needed here: a whole-byte member overwrites every cell it
     * touches outright, unlike a bitfield sharing a cell with a neighbour.
     */
    public static List<Expr<?>> toBytes(Expr<?> value, int n) {
        final Type type = value.getType();
        final List<Expr<?>> bytes = new ArrayList<>(n);
        if (type instanceof BvType bv) {
            final Expr<BvType> v = cast(value, bv);
            for (int j = 0; j < n; j++) {
                bytes.add(BvExprs.Extract(v, Int(8 * j), Int(8 * j + 8)));
            }
            return bytes;
        }
        if (type instanceof IntType) {
            final Expr<IntType> v = cast(value, IntType.getInstance());
            for (int j = 0; j < n; j++) {
                bytes.add(Mod(Div(v, pow2(8 * j)), pow2(8)));
            }
            return bytes;
        }
        throw new IllegalArgumentException(
                "Unsupported value type for a byte-laid-out union: " + type);
    }

    private static Expr<IntType> pow2(int exponent) {
        return Int(BigInteger.ONE.shiftLeft(exponent));
    }
}
