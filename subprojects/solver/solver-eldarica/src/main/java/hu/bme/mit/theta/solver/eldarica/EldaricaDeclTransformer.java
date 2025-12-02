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

import static ap.parser.IExpression.ConstantTerm2ITerm;
import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.solver.eldarica.Utils.PredTermFormula.wrap;
import static hu.bme.mit.theta.solver.eldarica.Utils.toSeq;

import ap.terfor.preds.Predicate;
import ap.types.MonoSortedPredicate;
import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import java.util.List;

final class EldaricaDeclTransformer {

    private final EldaricaTransformationManager transformer;
    private final EldaricaSymbolTable symbolTable;

    EldaricaDeclTransformer(
            final EldaricaTransformationManager transformer,
            final EldaricaSymbolTable symbolTable) {
        this.transformer = transformer;
        this.symbolTable = symbolTable;
    }

    public Utils.PredTermFormula toSymbol(final Decl<?> decl) {
        if (decl instanceof ConstDecl) {
            return transformConst((ConstDecl<?>) decl);
        } else {
            throw new UnsupportedOperationException("Cannot transform declaration: " + decl);
        }
    }

    private Utils.PredTermFormula transformConst(final ConstDecl<?> decl) {
        final Utils.PredTermFormula symbol;

        if (symbolTable.definesConst(decl)) {
            symbol = symbolTable.getSymbol(decl);
        } else {
            final Type type = decl.getType();

            final Tuple2<List<Type>, Type> extractedTypes = extractTypes(type);
            final List<Type> paramTypes = extractedTypes.get1();
            final Type returnType = extractedTypes.get2();

            if (paramTypes.isEmpty() && returnType.equals(BoolType.getInstance())) {

                symbol = wrap(new Predicate(decl.getName(), 0));
            } else if (paramTypes.isEmpty()) {
                symbol =
                        wrap(
                                ConstantTerm2ITerm(
                                        transformer
                                                .toSort(returnType)
                                                .newConstant(decl.getName())));
            } else {
                symbol =
                        wrap(
                                MonoSortedPredicate.apply(
                                        decl.getName(),
                                        toSeq(
                                                paramTypes.stream()
                                                        .map(transformer::toSort)
                                                        .toList())));
            }

            symbolTable.put(decl, symbol);
        }

        return symbol;
    }

    private Tuple2<List<Type>, Type> extractTypes(final Type type) {
        if (type instanceof FuncType<?, ?>) {
            final FuncType<?, ?> funcType = (FuncType<?, ?>) type;

            final Type paramType = funcType.getParamType();
            final Type resultType = funcType.getResultType();

            checkArgument(!(paramType instanceof FuncType), "Parameter type most not be function");

            final Tuple2<List<Type>, Type> subResult = extractTypes(resultType);
            final List<Type> paramTypes = subResult.get1();
            final Type newResultType = subResult.get2();
            final List<Type> newParamTypes =
                    ImmutableList.<Type>builder().add(paramType).addAll(paramTypes).build();
            final Tuple2<List<Type>, Type> result = Tuple2.of(newParamTypes, newResultType);

            return result;
        } else {
            return Tuple2.of(ImmutableList.of(), type);
        }
    }
}
