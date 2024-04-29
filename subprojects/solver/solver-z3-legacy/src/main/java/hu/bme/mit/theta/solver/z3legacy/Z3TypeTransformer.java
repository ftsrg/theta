/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.z3legacy;

import com.google.common.collect.Sets;
import com.microsoft.z3legacy.Context;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatType;

import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

final class Z3TypeTransformer {

    @SuppressWarnings("unused")
    private final Z3TransformationManager transformer;
    private final Context context;

    private final com.microsoft.z3legacy.BoolSort boolSort;
    private final com.microsoft.z3legacy.IntSort intSort;
    private final com.microsoft.z3legacy.RealSort realSort;
    private final Set<com.microsoft.z3legacy.BitVecSort> bvSorts;
    private final Set<com.microsoft.z3legacy.FPSort> fpSorts;

    Z3TypeTransformer(final Z3TransformationManager transformer, final Context context) {
        this.context = context;
        this.transformer = transformer;

        boolSort = context.mkBoolSort();
        intSort = context.mkIntSort();
        realSort = context.mkRealSort();
        bvSorts = Sets.synchronizedNavigableSet(new TreeSet<>());
        fpSorts = Sets.synchronizedNavigableSet(new TreeSet<>());
    }

    public com.microsoft.z3legacy.Sort toSort(final Type type) {
        if (type instanceof BoolType) {
            return boolSort;
        } else if (type instanceof IntType) {
            return intSort;
        } else if (type instanceof RatType) {
            return realSort;
        } else if (type instanceof BvType) {
            final BvType bvType = (BvType) type;
            final Optional<com.microsoft.z3legacy.BitVecSort> bvSort = bvSorts.stream()
                    .filter(sort -> sort.getSize() == bvType.getSize()).findAny();
            if (bvSort.isPresent()) {
                return bvSort.get();
            } else {
                final com.microsoft.z3legacy.BitVecSort newBvSort = context.mkBitVecSort(
                        bvType.getSize());
                bvSorts.add(newBvSort);
                return newBvSort;
            }
        } else if (type instanceof FpType) {
            final FpType fpType = (FpType) type;
            final Optional<com.microsoft.z3legacy.FPSort> fpSort = fpSorts.stream().filter(
                    sort -> sort.getEBits() == fpType.getExponent()
                            && sort.getSBits() == fpType.getSignificand()).findAny();
            if (fpSort.isPresent()) {
                return fpSort.get();
            } else {
                final com.microsoft.z3legacy.FPSort newFpSort = context.mkFPSort(fpType.getExponent(),
                        fpType.getSignificand());
                fpSorts.add(newFpSort);
                return newFpSort;
            }
        } else if (type instanceof ArrayType) {
            final ArrayType<?, ?> arrayType = (ArrayType<?, ?>) type;
            final com.microsoft.z3legacy.Sort indexSort = toSort(arrayType.getIndexType());
            final com.microsoft.z3legacy.Sort elemSort = toSort(arrayType.getElemType());
            return context.mkArraySort(indexSort, elemSort);
        } else {
            throw new UnsupportedOperationException(
                    "Unsupporte type: " + type.getClass().getSimpleName());
        }
    }

    public void reset() {
        bvSorts.clear();
    }

}
