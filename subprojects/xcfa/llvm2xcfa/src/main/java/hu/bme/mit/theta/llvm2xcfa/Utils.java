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

package hu.bme.mit.theta.llvm2xcfa;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.llvm2xcfa.handlers.Instruction;
import hu.bme.mit.theta.llvm2xcfa.handlers.arguments.Argument;
import hu.bme.mit.theta.llvm2xcfa.handlers.arguments.LocalArgument;
import hu.bme.mit.theta.llvm2xcfa.handlers.arguments.RegArgument;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.BlockState;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.FunctionState;
import hu.bme.mit.theta.xcfa.model.EmptyMetaData;
import hu.bme.mit.theta.xcfa.model.NopLabel;
import hu.bme.mit.theta.xcfa.model.StmtLabel;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.math.BigInteger;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class Utils {
    private static final int doublePrecision = 1 << 8;
    public static ArithmeticType arithmeticType;

    public static Type createType(String type) {
        type = type.replaceAll("\\*", "");
        String arrayPattern = "\\[([1-9][0-9]*) x (.*)]";
        Pattern pattern = Pattern.compile(arrayPattern);
        Matcher matcher = pattern.matcher(type);
        if (matcher.find()) {
            Integer size = Integer.parseInt(matcher.group(1));
            type = matcher.group(2);
            return Array(Int(), createType(type));
        }

        switch (type) {
            case "double":
            case "float":
                return Rat();
            case "i64":
                if (arithmeticType == ArithmeticType.bitvector) return BvType.of(64);
            case "i32":
                if (arithmeticType == ArithmeticType.bitvector) return BvType.of(32);
            case "i16":
                if (arithmeticType == ArithmeticType.bitvector) return BvType.of(16);
            case "i8":
                if (arithmeticType == ArithmeticType.bitvector) return BvType.of(8);
                return Int();
            case "i1":
                return Bool();
            default:
//                new RuntimeException("Type " + type + " not known! (Using 32 bit int instead)").printStackTrace();
                if (arithmeticType == ArithmeticType.bitvector) return BvType.of(32);
                return Int();
        }
    }

    public static VarDecl<? extends Type> createVariable(String name, String type) {
        Type t;
        t = createType(type);
        return Var(name, t);
    }

    public static LitExpr<? extends Type> parseConstant(Type type, String value) {
        if (type instanceof RatType)
            return RatLitExpr.of(BigInteger.valueOf((long) (Float.parseFloat(value) * doublePrecision)), BigInteger.valueOf(doublePrecision));
        return IntLitExpr.of(new BigInteger(value));
    }

    public static LitExpr<? extends Type> createConstant(String value) {
        return createConstant(Int(), value);
    }

    public static LitExpr<? extends Type> createConstant(Type type, String value) {
        String[] arguments = value.split(" ");
        if (arguments.length != 2) {
            System.err.println("Constant should be of form \"(type=[a-zA-Z0-9]*) (value=[\\.0-9fe+-]*)\", got: " + value);
            return getDefaultValue(type);

        }

        switch (arguments[0]) {
            case "double":
            case "float":
                return RatLitExpr.of(BigInteger.valueOf((long) (Float.parseFloat(arguments[1]) * doublePrecision)), BigInteger.valueOf(doublePrecision));
            case "i64":
                if (arithmeticType == ArithmeticType.bitvector)
                    return BvUtils.bigIntegerToNeutralBvLitExpr(new BigInteger(arguments[1]), 64);
            case "i32":
                if (arithmeticType == ArithmeticType.bitvector)
                    return BvUtils.bigIntegerToNeutralBvLitExpr(new BigInteger(arguments[1]), 32);
            case "i16":
                if (arithmeticType == ArithmeticType.bitvector)
                    return BvUtils.bigIntegerToNeutralBvLitExpr(new BigInteger(arguments[1]), 16);
            case "i8":
                if (arithmeticType == ArithmeticType.bitvector)
                    return BvUtils.bigIntegerToNeutralBvLitExpr(new BigInteger(arguments[1]), 8);
                return IntLitExpr.of(new BigInteger(arguments[1]));
            case "i1":
                return BoolLitExpr.of(arguments[1].equals("true"));
            default:
                new RuntimeException("Type " + arguments[0] + " not known! (Using int32(0) instead)").printStackTrace();
                if (arithmeticType == ArithmeticType.bitvector)
                    return BvUtils.bigIntegerToNeutralBvLitExpr(new BigInteger("0"), 32);
                return IntLitExpr.of(BigInteger.ZERO);
        }
    }

    private static LitExpr<? extends Type> getDefaultValue(Type type) {
        if (type instanceof RatType) return RatLitExpr.of(BigInteger.ZERO, BigInteger.ONE);
        else if (type instanceof BvType)
            return BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, ((BvType) type).getSize());
        else if (type instanceof ArrayType) return ArrayLitExpr.of(
                List.of(Tuple2.of(IntLitExpr.of(BigInteger.ZERO), cast(getDefaultValue(((ArrayType<?, ?>) type).getElemType()), ((ArrayType<?, ?>) type).getElemType()))),
                cast(getDefaultValue(((ArrayType<?, ?>) type).getElemType()), ((ArrayType<?, ?>) type).getElemType()),
                ArrayType.of(Int(), ((ArrayType<?, ?>) type).getElemType()));
        return IntLitExpr.of(BigInteger.ZERO);
    }

    public static VarDecl<?> getOrCreateVar(FunctionState functionState, Argument regArgument) {
        VarDecl<?> var;
        Tuple2<VarDecl<?>, Integer> objects = functionState.getLocalVars().get(regArgument.getName());
        if (objects == null) {
            var = Var(regArgument.getName(), regArgument.getType());
            functionState.getProcedureBuilder().getVars().add(var);
            functionState.getLocalVars().put(regArgument.getName(), Tuple2.of(var, 1));
            functionState.getValues().put(regArgument.getName(), var.getRef());
            return var;
        } else if (!objects.get1().getType().equals(regArgument.getType())) {
            String typedName = regArgument.getName() + "_" + regArgument.getType().toString();
            objects = functionState.getLocalVars().get(typedName);
            if (objects == null) {
                var = Var(typedName, regArgument.getType());
                functionState.getProcedureBuilder().getVars().add(var);
                functionState.getLocalVars().put(typedName, Tuple2.of(var, 1));
                functionState.getValues().put(typedName, var.getRef());
                return var;
            } else return objects.get1();
        } else {
            return objects.get1();
        }
    }

    public static void foldExpression(Instruction instruction, FunctionState functionState, BlockState blockState, String opName, Expr<?> op, int ref) {
        //noinspection OptionalGetWithoutIsPresent
        RegArgument ret = instruction.getRetVar().get();
        if (ret instanceof LocalArgument) {
            XcfaLocation loc = new XcfaLocation(blockState.getName() + "_" + blockState.getBlockCnt());
            VarDecl<?> lhs = Utils.getOrCreateVar(functionState, ret);
            Stmt stmt = Assign(cast(lhs, lhs.getType()), cast(op, lhs.getType()));
            XcfaEdge edge;
            if (!lhs.getRef().equals(op))
                edge = new XcfaEdge(blockState.getLastLocation(), loc, new StmtLabel(stmt, EmptyMetaData.INSTANCE), new LlvmMetadata(instruction.getLineNumber()));
            else
                edge = new XcfaEdge(blockState.getLastLocation(), loc, NopLabel.INSTANCE, new LlvmMetadata(instruction.getLineNumber()));
            functionState.getProcedureBuilder().addLoc(loc);
            functionState.getProcedureBuilder().addEdge(edge);
            blockState.setLastLocation(loc);
        } else {
            if (functionState.getLocalVars().containsKey(opName)) {
                Tuple2<VarDecl<?>, Integer> oldVar = functionState.getLocalVars().get(opName);
                functionState.getLocalVars().put(ret.getName(), Tuple2.of(oldVar.get1(), oldVar.get2() + ref));
            }
            functionState.getValues().put(ret.getName(), op);
        }
    }

}
