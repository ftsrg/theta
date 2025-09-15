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

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.functype.FuncType;
import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.SolverContext;

final class JavaSMTDeclTransformer {

    private final JavaSMTTransformationManager transformer;
    private final JavaSMTSymbolTable symbolTable;
    private final SolverContext context;

    private int symbolCount;

    JavaSMTDeclTransformer(
            final JavaSMTTransformationManager transformer,
            final JavaSMTSymbolTable symbolTable,
            final SolverContext context) {
        this.transformer = transformer;
        this.symbolTable = symbolTable;
        this.context = context;
        this.symbolCount = 0;
    }

    public Formula toSymbol(final Decl<?> decl) {
        if (decl instanceof ConstDecl) {
            return transformConst((ConstDecl<?>) decl);
        } else {
            throw new UnsupportedOperationException("Cannot transform declaration: " + decl);
        }
    }

    private Formula transformConst(final ConstDecl<?> decl) {
        final Formula symbol;

        if (symbolTable.definesConstAsFormula(decl)) {
            symbol = symbolTable.getSymbolAsFormula(decl);
        } else {
            final Type type = decl.getType();

            final Tuple2<List<Type>, Type> extractedTypes = extractTypes(type);
            final List<Type> paramTypes = extractedTypes.get1();
            final Type returnType = extractedTypes.get2();

            final FormulaType<?> returnSort = transformer.toSort(returnType);
            final List<? extends FormulaType<?>> paramSorts =
                    paramTypes.stream().map(transformer::toSort).toList();

            if (!paramSorts.isEmpty()) {
                throw new JavaSMTSolverException("Function consts not yet supported.");
            }

            // Enums can't be yet handled by formulamanager directly
            if (returnSort.isEnumerationType()) {
                symbol =
                        context.getFormulaManager()
                                .getEnumerationFormulaManager()
                                .makeVariable(
                                        symbolNameFor(decl),
                                        (FormulaType.EnumerationFormulaType) returnSort);
            } else {
                symbol = context.getFormulaManager().makeVariable(returnSort, symbolNameFor(decl));
            }

            symbolTable.put(decl, symbol);
        }

        return symbol;
    }

    private Tuple2<List<Type>, Type> extractTypes(final Type type) {
        if (type instanceof FuncType<?, ?> funcType) {

            final Type paramType = funcType.getParamType();
            final Type resultType = funcType.getResultType();

            checkArgument(!(paramType instanceof FuncType), "Parameter type most not be function");

            final Tuple2<List<Type>, Type> subResult = extractTypes(resultType);
            final List<Type> paramTypes = subResult.get1();
            final Type newResultType = subResult.get2();
            final List<Type> newParamTypes =
                    ImmutableList.<Type>builder().add(paramType).addAll(paramTypes).build();
            return Tuple2.of(newParamTypes, newResultType);
        } else {
            return Tuple2.of(ImmutableList.of(), type);
        }
    }

    private String symbolNameFor(final Decl<?> decl) {
        return String.format("%s_%d", decl.getName(), symbolCount++);
    }
}
