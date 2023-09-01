/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.frontend.chc;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCParser;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTypeTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTypeTransformer;
import hu.bme.mit.theta.xcfa.model.EmptyMetaData;
import hu.bme.mit.theta.xcfa.model.StmtLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.xcfa.passes.UtilsKt.changeVars;

public class ChcUtils {
    // TODO eliminate static fields (re-runs?)
    private static GenericSmtLibSymbolTable initialSymbolTable = new GenericSmtLibSymbolTable();
    private static GenericSmtLibSymbolTable symbolTable;
    private static SmtLibTypeTransformer typeTransformer = new GenericSmtLibTypeTransformer(null);
    private static SmtLibTermTransformer termTransformer = new GenericSmtLibTermTransformer(initialSymbolTable);
    private static CharStream charStream;

    private ChcUtils() {
    }

    public static void init(CharStream cs) {
        initialSymbolTable = new GenericSmtLibSymbolTable();
        typeTransformer = new GenericSmtLibTypeTransformer(null);
        termTransformer = new GenericSmtLibTermTransformer(initialSymbolTable);
        charStream = cs;
    }

    public static List<XcfaLabel> getTailConditionLabels(CHCParser.Chc_tailContext tail, Map<String, VarDecl<?>> localVars) {
        List<XcfaLabel> labels = new ArrayList<>();
        tail.i_formula().forEach(i_formula -> {  // null as SmtLibModel, because it is unused
            Expr<BoolType> expr = termTransformer.toExpr(getOriginalText(i_formula), Bool(), new SmtLibModel(Collections.emptyMap()));
            List<ConstDecl<?>> exprVars = new ArrayList<>();
            ExprUtils.collectConstants(expr, exprVars);
            Map<Decl<?>, VarDecl<?>> varsToLocal = new HashMap<>();
            for (Decl<?> var : exprVars) {
                if (localVars.containsKey(var.getName())) {
                    varsToLocal.put(var, localVars.get(var.getName()));
                }
            }
            Expr<BoolType> replacedExpr = changeVars(expr, varsToLocal);
            labels.add(new StmtLabel(AssumeStmt.of(replacedExpr), EmptyMetaData.INSTANCE));
        });
        return labels;
    }

    public static String getOriginalText(ParserRuleContext ctx) {
        return charStream.getText(new Interval(ctx.start.getStartIndex(), ctx.stop.getStopIndex()));
    }

    public static Map<String, VarDecl<?>> createVars(XcfaProcedureBuilder builder, List<CHCParser.Var_declContext> var_decls) {
        resetSymbolTable();
        Map<String, VarDecl<?>> vars = new HashMap<>();
        for (CHCParser.Var_declContext var_decl : var_decls) {
            String name = var_decl.symbol().getText();
            String varName = name + "_" + builder.getEdges().size();
            Type type = transformSort(var_decl.sort());
            VarDecl<?> var = Decls.Var(varName, type);
            builder.addVar(var);
            transformConst(Decls.Const(name, type), false);
            vars.put(name, var);
        }
        return vars;
    }

    public static void resetSymbolTable() {
        symbolTable = new GenericSmtLibSymbolTable(initialSymbolTable);
        termTransformer = new GenericSmtLibTermTransformer(symbolTable);

    }

    public static Type transformSort(final CHCParser.SortContext ctx) {
        final String name = ctx.identifier().symbol().getText();
        switch (name) {
            case "Int":
                return Int();
            case "Bool":
                return Bool();
            case "Real":
                return Rat();
            case "BitVec":
                assert ctx.identifier().index().size() == 1;
                return BvExprs.BvType(Integer.parseInt(ctx.identifier().index().get(0).getText()));
            case "Array":
                assert ctx.sort().size() == 2;
                return Array(transformSort(ctx.sort().get(0)), transformSort(ctx.sort().get(1)));
            default:
                throw new UnsupportedOperationException();
        }
    }

    public static void transformConst(final ConstDecl<?> decl, boolean initial) {
        final Type type = decl.getType();

        final Tuple2<List<Type>, Type> extractedTypes = extractTypes(type);
        final List<Type> paramTypes = extractedTypes.get1();
        final Type returnType = extractedTypes.get2();

        final String returnSort = typeTransformer.toSort(returnType);
        final String[] paramSorts = paramTypes.stream().map(typeTransformer::toSort)
                .toArray(String[]::new);

        final String symbolName = decl.getName();
        final String symbolDeclaration = String.format(
                "(declare-fun %s (%s) %s)",
                symbolName, String.join(" ", paramSorts), returnSort
        );
        (initial ? initialSymbolTable : symbolTable).put(decl, symbolName, symbolDeclaration);
    }

    public static Tuple2<List<Type>, Type> extractTypes(final Type type) {
        if (type instanceof FuncType<?, ?>) {
            final FuncType<?, ?> funcType = (FuncType<?, ?>) type;

            final Type paramType = funcType.getParamType();
            final Type resultType = funcType.getResultType();

            checkArgument(!(paramType instanceof FuncType));

            final Tuple2<List<Type>, Type> subResult = extractTypes(resultType);
            final List<Type> paramTypes = subResult.get1();
            final Type newResultType = subResult.get2();
            final List<Type> newParamTypes = ImmutableList.<Type>builder().add(paramType).addAll(paramTypes).build();
            final Tuple2<List<Type>, Type> result = Tuple2.of(newParamTypes, newResultType);

            return result;
        } else {
            return Tuple2.of(ImmutableList.of(), type);
        }
    }
}
