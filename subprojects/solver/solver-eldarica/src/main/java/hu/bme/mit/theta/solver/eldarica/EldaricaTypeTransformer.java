/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.eldarica;

import static hu.bme.mit.theta.solver.eldarica.Utils.toSeq;

import ap.theories.arrays.ExtArray;
import ap.theories.bitvectors.ModuloArithmetic;
import ap.types.Sort;
import ap.types.Sort$;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatType;
import java.util.*;

final class EldaricaTypeTransformer {

    private final Map<ArrayType<?, ?>, Sort> arraySortMap = new LinkedHashMap<>();

    public Sort toSort(final Type type) {
        if (type instanceof BoolType) {
            return Sort$.MODULE$.Bool();
        } else if (type instanceof IntType) {
            return Sort.Integer$.MODULE$;
        } else if (type instanceof RatType) {
            throw new UnsupportedOperationException("Reals/Rats not yet supported");
        } else if (type instanceof BvType) {
            return ModuloArithmetic.UnsignedBVSort$.MODULE$.apply(((BvType) type).getSize());
        } else if (type instanceof FpType) {
            throw new UnsupportedOperationException("Fps not yet supported");
        } else if (type instanceof ArrayType arrayType) {
            return arraySortMap.computeIfAbsent(
                    arrayType,
                    (t) ->
                            new ExtArray(toSeq(toSort(t.getIndexType())), toSort(t.getElemType()))
                                    .sort());
        } else if (type instanceof EnumType) {
            throw new UnsupportedOperationException("Enums not yet supported");
        } else {
            throw new UnsupportedOperationException(
                    "Unsupported type: " + type.getClass().getSimpleName());
        }
    }
}
