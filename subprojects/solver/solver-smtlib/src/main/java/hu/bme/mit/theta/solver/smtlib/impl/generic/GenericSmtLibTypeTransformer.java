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
package hu.bme.mit.theta.solver.smtlib.impl.generic;

import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;
import hu.bme.mit.theta.common.DispatchTable;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTransformationManager;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTypeTransformer;

import java.util.concurrent.ExecutionException;

public class GenericSmtLibTypeTransformer implements SmtLibTypeTransformer {

    private static final int CACHE_SIZE = 1000;

    @SuppressWarnings("unused")
    private final SmtLibTransformationManager transformer;

    private final Cache<Type, String> typeToSmtLib;
    private final DispatchTable<String> table;

    public GenericSmtLibTypeTransformer(final SmtLibTransformationManager transformer) {
        this.transformer = transformer;

        typeToSmtLib = CacheBuilder.newBuilder().maximumSize(CACHE_SIZE).build();

        table = buildDispatchTable(DispatchTable.builder()).build();
    }

    protected DispatchTable.Builder<String> buildDispatchTable(DispatchTable.Builder<String> builder) {
        builder
                .addCase(BoolType.class, this::boolType)
                .addCase(IntType.class, this::intType)
                .addCase(RatType.class, this::ratType)
                .addCase(BvType.class, this::bvType)
                .addCase(FpType.class, this::fpType)
                .addCase(EnumType.class, this::enumType)
                .addCase(ArrayType.class, this::arrayType);
        return builder;
    }

    @Override
    public final String toSort(final Type type) {
        try {
            return typeToSmtLib.get(type, () -> table.dispatch(type));
        } catch (final ExecutionException e) {
            throw new AssertionError();
        }
    }

    protected String boolType(final BoolType type) {
        return "Bool";
    }

    protected String intType(final IntType type) {
        return "Int";
    }

    protected String ratType(final RatType type) {
        return "Real";
    }

    protected String bvType(final BvType type) {
        return String.format("(_ BitVec %d)", type.getSize());
    }

    protected String fpType(final FpType type) {
        return String.format("(_ FloatingPoint %d %d)", type.getExponent(), type.getSignificand());
    }

    protected String arrayType(final ArrayType<?, ?> type) {
        return String.format("(Array %s %s)", toSort(type.getIndexType()),
                toSort(type.getElemType()));
    }

    protected String enumType(final EnumType type) {
        return type.getName();
    }
}
