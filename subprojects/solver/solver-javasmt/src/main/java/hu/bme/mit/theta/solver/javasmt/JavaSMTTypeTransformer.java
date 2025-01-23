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
package hu.bme.mit.theta.solver.javasmt;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatType;
import java.util.HashMap;
import java.util.Map;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.SolverContext;

final class JavaSMTTypeTransformer {

    private final SolverContext solverContext;
    private final FormulaType<BooleanFormula> boolSort;
    private final FormulaType<IntegerFormula> intSort;
    private final FormulaType<RationalFormula> realSort;
    private final Map<String, FormulaType<EnumerationFormula>> enumSorts;

    JavaSMTTypeTransformer(final SolverContext solverContext) {
        this.solverContext = solverContext;
        boolSort = FormulaType.BooleanType;
        intSort = FormulaType.IntegerType;
        realSort = FormulaType.RationalType;
        enumSorts = new HashMap<>();
    }

    public FormulaType<?> toSort(final Type type) {
        if (type instanceof BoolType) {
            return boolSort;
        } else if (type instanceof IntType) {
            return intSort;
        } else if (type instanceof RatType) {
            return realSort;
        } else if (type instanceof EnumType enumType) {
            return enumSorts.computeIfAbsent(
                    enumType.getName(),
                    name ->
                            solverContext
                                    .getFormulaManager()
                                    .getEnumerationFormulaManager()
                                    .declareEnumeration(name, enumType.getLongValues()));
        } else if (type instanceof BvType bvType) {
            return FormulaType.getBitvectorTypeWithSize(bvType.getSize());
        } else if (type instanceof FpType fpType) {
            return FormulaType.getFloatingPointType(fpType.getExponent(), fpType.getSignificand());
        } else if (type instanceof ArrayType<?, ?> arrayType) {
            final FormulaType<?> indexSort = toSort(arrayType.getIndexType());
            final FormulaType<?> elemSort = toSort(arrayType.getElemType());
            return FormulaType.getArrayType(indexSort, elemSort);
        } else {
            throw new UnsupportedOperationException(
                    "Unsupported type: " + type.getClass().getSimpleName());
        }
    }
}
