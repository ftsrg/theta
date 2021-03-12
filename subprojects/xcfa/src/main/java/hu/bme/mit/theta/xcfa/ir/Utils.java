package hu.bme.mit.theta.xcfa.ir;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.common.Tuple4;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntEqExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.xcfa.XCFA;

import java.math.BigInteger;
import java.util.*;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

public class Utils {

    private static final int FLOAT_DIGITS = 5;

    public static Type createType(IRType type) {
        switch (type) {
            case INTEGER32: return Int();
            case FLOAT64:   return Rat();
            default:
                throw new IllegalStateException("Unexpected value: " + type);
        }
    }

    public static VarDecl<? extends Type> createVariable(String name, IRType type) {
        Type t = createType(type);
        return Var(name, t);
    }

    public static LitExpr<? extends Type> createConstant(IRType type, String value) {
        switch (type) {
            case INTEGER32: return IntLitExpr.of(new BigInteger(value));
            case FLOAT64:
                float v = Float.parseFloat(value);
                return RatLitExpr.of(BigInteger.valueOf((long)(v*(1 << FLOAT_DIGITS))), BigInteger.valueOf(1 << FLOAT_DIGITS));
            default:
                throw new IllegalStateException("Unexpected value: " + type);
        }
    }

    public static Collection<String> handleProcedure(
            Tuple3<String, Optional<IRType>, List<Tuple2<IRType, String>>> function,
            XCFA.Process.Procedure.Builder procedureBuilder,
            SSAProvider ssa,
            Map<String, VarDecl<?>> globalVarLut) {

        Map<String, VarDecl<?>> localVarLut = new HashMap<>();

        // Adding params
        for (Tuple2<IRType, String> param : function.get3()) {
            VarDecl<?> var = createVariable(param.get2(), param.get1());
            procedureBuilder.createParam(var);
            localVarLut.put(param.get2(), var);
        }

        // Adding final location
        XCFA.Process.Procedure.Location finalLoc = new XCFA.Process.Procedure.Location(function.get1() + "_final", new HashMap<>());
        procedureBuilder.addLoc(finalLoc);
        procedureBuilder.setFinalLoc(finalLoc);

        // Adding return variable
        Optional<VarDecl<? extends Type>> retVar = Optional.empty();
        if(function.get2().isPresent()) {
            retVar = Optional.of(createVariable(function.get1() + "_ret", function.get2().get()));
            procedureBuilder.setRtype(createType(function.get2().get()));
            procedureBuilder.setResult(retVar.get());
        }

        // Adding blocks and first location
        List<String> blocks = ssa.getBlocks(function.get1());
        Map<String, XCFA.Process.Procedure.Location> locationLut = new HashMap<>();
        boolean first = true;
        for (String block : blocks) {
            XCFA.Process.Procedure.Location loc = new XCFA.Process.Procedure.Location(block, new HashMap<>());
            locationLut.put(block, loc);
            procedureBuilder.addLoc(loc);
            if(first) {
                procedureBuilder.setInitLoc(loc);
                first = false;
            }
        }

        Map<Tuple2<String, String>, Tuple3<XCFA.Process.Procedure.Location, XCFA.Process.Procedure.Location, List<Stmt>>> terminatorEdges = new HashMap<>();

        // Handling instructions
        for (String block : locationLut.keySet()) {
            XCFA.Process.Procedure.Location lastLoc = locationLut.get(block);
            Map<String, Expr<?>> valueLut = new HashMap<>();
            Integer[] cnt = new Integer[1]; // to create by-ref passable counter
            for (Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction : ssa.getInstructions(block)) {
                checkState(!(lastLoc.isEndLoc() || lastLoc.isErrorLoc()), "No instruction can occur after a final or error location!");
                switch(instruction.get1()) {
                    case RET:
                        lastLoc = ret(procedureBuilder, valueLut, finalLoc, retVar, lastLoc, instruction);
                        break;
                    case BR:
                        lastLoc = br(procedureBuilder, valueLut, locationLut, finalLoc, lastLoc, instruction, terminatorEdges, block);
                        break;
                    case SWITCH:
                        lastLoc = sw(procedureBuilder, valueLut, locationLut, finalLoc, lastLoc, instruction, terminatorEdges, block);
                        break;
                    case ADD:
                        add(valueLut, instruction);
                        break;
                    case SUB:
                        sub(valueLut, instruction);
                        break;
                    case MUL:
                        mul(valueLut, instruction);
                        break;
                    case SDIV:
                        div(valueLut, instruction);
                        break;
                    case SREM:
                        rem(valueLut, instruction);
                        break;
                    case ALLOCA:
                        alloca(procedureBuilder, localVarLut, instruction);
                        break;
                    case LOAD:
                        load(localVarLut, valueLut, instruction);
                        break;
                    case STORE:
                        lastLoc = store(function, localVarLut, lastLoc, valueLut, cnt, instruction);
                        break;
                    case ICMP:
                        cmp(valueLut, instruction);
                        break;
                    case PHI:
                        phi(procedureBuilder, localVarLut, terminatorEdges, block, valueLut, cnt, instruction);
                        break;
                    case CALL:
                        System.out.println("call");
                        break;
                    default:
                        throw new IllegalStateException("Unexpected value: " + instruction.get1());
                }
            }
        }

    }

    private static void phi(XCFA.Process.Procedure.Builder procedureBuilder, Map<String, VarDecl<?>> localVarLut, Map<Tuple2<String, String>, Tuple3<XCFA.Process.Procedure.Location, XCFA.Process.Procedure.Location, List<Stmt>>> terminatorEdges, String block, Map<String, Expr<?>> valueLut, Integer[] cnt, Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        checkState(instruction.get3().size() % 2 == 1, "Phi node should have an odd number of arguments");
        checkState(instruction.get3().get(0).get1().isPresent(), "Return type must be present in phi node!");
        VarDecl<?> phiVar = createVariable(block +"_"+ cnt[0]++, instruction.get3().get(0).get1().get());
        procedureBuilder.getLocalVars().put(phiVar, null);
        localVarLut.put(phiVar.getName(), phiVar);
        for(int i = 0; i < (instruction.get3().size() + 1) / 2; ++i) {
            String blockName = instruction.get3().get(2*i + 1).get2();
            Expr<?> value = getExpr(valueLut, instruction, 2*i + 2);
            checkState(terminatorEdges.containsKey(Tuple2.of(block, blockName)), "Edge does not exist!");
            terminatorEdges.get(Tuple2.of(block, blockName)).get3().add(Assign(phiVar, value));
        }
    }


    private static void cmp(Map<String, Expr<?>> valueLut, Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<IntType> lhs = getExpr(valueLut, instruction, paramSize - 2);
        Expr<IntType> rhs = getExpr(valueLut, instruction, paramSize - 1);

        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        switch(instruction.get3().get(0).get2()) {
            case "eq": valueLut.put(instruction.get2().get(), Eq(lhs, rhs)); break;
            case "ne": valueLut.put(instruction.get2().get(), Neq(lhs, rhs)); break;
            case "ugt": case "sgt": valueLut.put(instruction.get2().get(), Gt(lhs, rhs)); break;
            case "uge": case "sge": valueLut.put(instruction.get2().get(), Geq(lhs, rhs)); break;
            case "ult": case "slt": valueLut.put(instruction.get2().get(), Lt(lhs, rhs)); break;
            case "ule": case "sle": valueLut.put(instruction.get2().get(), Leq(lhs, rhs)); break;
            default:
                throw new IllegalStateException("Unexpected value: " + instruction.get3().get(0).get2());
        }

    }


    private static XCFA.Process.Procedure.Location store(Tuple3<String, Optional<IRType>, List<Tuple2<IRType, String>>> function, Map<String, VarDecl<?>> localVarLut, XCFA.Process.Procedure.Location lastLoc, Map<String, Expr<?>> valueLut, Integer[] cnt, Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        checkState(paramSize == 2, "Store should have two arguments");
        XCFA.Process.Procedure.Location loc = new XCFA.Process.Procedure.Location(function.get1() + "_" + cnt[0]++, new HashMap<>());
        Stmt stmt = Assign(localVarLut.get(instruction.get3().get(0).get2()), getExpr(valueLut, instruction, paramSize - 1));
        XCFA.Process.Procedure.Edge edge = new XCFA.Process.Procedure.Edge(lastLoc, loc, List.of(stmt));
        lastLoc = loc;
        return lastLoc;
    }

    private static void load(Map<String, VarDecl<?>> localVarLut, Map<String, Expr<?>> valueLut, Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        checkState(instruction.get3().size() >= 2);
        checkState(instruction.get2().isPresent(), "Load must load into a variable");
        valueLut.put(instruction.get2().get(), localVarLut.get(instruction.get3().get(1).get2()).getRef());
    }

    private static void alloca(XCFA.Process.Procedure.Builder procedureBuilder, Map<String, VarDecl<?>> localVarLut, Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        checkState(instruction.get2().isPresent(), "Alloca must have a variable tied to it");
        VarDecl<?> var = createVariable(instruction.get2().get(), IRType.INTEGER32);
        procedureBuilder.getLocalVars().put(var, null);
        localVarLut.put(instruction.get2().get(), var);
    }

    private static void rem(Map<String, Expr<?>> valueLut, Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<IntType> lhs = getExpr(valueLut, instruction, paramSize - 2);
        Expr<IntType> rhs = getExpr(valueLut, instruction, paramSize - 1);

        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        valueLut.put(instruction.get2().get(), Rem(lhs, rhs));
    }

    private static void div(Map<String, Expr<?>> valueLut, Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<IntType> lhs = getExpr(valueLut, instruction, paramSize - 2);
        Expr<IntType> rhs = getExpr(valueLut, instruction, paramSize - 1);

        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        valueLut.put(instruction.get2().get(), Div(lhs, rhs));
    }

    private static void mul(Map<String, Expr<?>> valueLut, Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<IntType> lhs = getExpr(valueLut, instruction, paramSize - 2);
        Expr<IntType> rhs = getExpr(valueLut, instruction, paramSize - 1);

        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        valueLut.put(instruction.get2().get(), Mul(lhs, rhs));
    }

    private static void sub(Map<String, Expr<?>> valueLut, Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<IntType> lhs = getExpr(valueLut, instruction, paramSize - 2);
        Expr<IntType> rhs = getExpr(valueLut, instruction, paramSize - 1);

        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        valueLut.put(instruction.get2().get(), Sub(lhs, rhs));
    }

    private static void add(Map<String, Expr<?>> valueLut, Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<IntType> lhs = getExpr(valueLut, instruction, paramSize - 2);
        Expr<IntType> rhs = getExpr(valueLut, instruction, paramSize - 1);

        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        valueLut.put(instruction.get2().get(), Add(lhs, rhs));
    }

    private static Expr<IntType> getExpr(Map<String, Expr<?>> valueLut, Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction, int i) {
        Expr<IntType> expr;
        Tuple2<Optional<IRType>, String> param1 = instruction.get3().get(i);
        if (param1.get1().isPresent()) {
            //noinspection unchecked
            expr = (Expr<IntType>) createConstant(param1.get1().get(), param1.get2());
        } else {
            //noinspection unchecked
            expr = (Expr<IntType>) valueLut.get(param1.get2());
        }
        return expr;
    }

    private static XCFA.Process.Procedure.Location sw(XCFA.Process.Procedure.Builder procedureBuilder, Map<String, Expr<?>> valueLut, Map<String, XCFA.Process.Procedure.Location> locationLut, XCFA.Process.Procedure.Location finalLoc, XCFA.Process.Procedure.Location lastLoc, Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction, Map<Tuple2<String, String>, Tuple3<XCFA.Process.Procedure.Location, XCFA.Process.Procedure.Location, List<Stmt>>> terminatorEdges, String block) {
        checkState(instruction.get3().size() % 2 == 0, "Switch has wrong number of arguments");
        //noinspection unchecked
        Expr<IntType> expr = (Expr<IntType>) valueLut.get(instruction.get3().get(0).get2());
        Expr<BoolType> defaultBranch = null;
        for (int i = 0; i < (instruction.get3().size() / 2) - 1; ++i) {
            XCFA.Process.Procedure.Location loc = locationLut.get(instruction.get3().get(2 + 2*i + 1).get2());
            checkState(valueLut.get(instruction.get3().get(0).get2()).getType() instanceof IntType, "Only IntTypes are supported!");
            Tuple2<Optional<IRType>, String> param = instruction.get3().get(2 + 2 * i);
            IntEqExpr eq;
            if(param.get1().isPresent()) {
                //noinspection unchecked
                eq = Eq(expr, (Expr<IntType>) createConstant(param.get1().get(), param.get2()));
            } else {
                //noinspection unchecked
                eq = Eq(expr, (Expr<IntType>) valueLut.get(param.get2()));
            }
            if(defaultBranch == null) defaultBranch = eq;
            else defaultBranch = BoolExprs.Or(defaultBranch, eq);

            AssumeStmt assume = Assume(eq);
            terminatorEdges.put(Tuple2.of(block, loc.getName()), Tuple3.of(lastLoc, loc, new ArrayList<>(List.of(assume))));
        }
        XCFA.Process.Procedure.Location loc = locationLut.get(instruction.get3().get(1).get2());
        checkState(valueLut.get(instruction.get3().get(1).get2()).getType() instanceof IntType, "Only IntTypes are supported!");
        XCFA.Process.Procedure.Edge edge = new XCFA.Process.Procedure.Edge(lastLoc, loc, List.of(Assume(BoolExprs.Not(defaultBranch))));
        procedureBuilder.addEdge(edge);
        return finalLoc; // to ensure no further edges get added
    }

    private static XCFA.Process.Procedure.Location br(XCFA.Process.Procedure.Builder procedureBuilder, Map<String, Expr<?>> valueLut, Map<String, XCFA.Process.Procedure.Location> locationLut, XCFA.Process.Procedure.Location finalLoc, XCFA.Process.Procedure.Location lastLoc, Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction, Map<Tuple2<String, String>, Tuple3<XCFA.Process.Procedure.Location, XCFA.Process.Procedure.Location, List<Stmt>>> terminatorEdges, String block) {
        switch(instruction.get3().size()) {
            case 1:
                XCFA.Process.Procedure.Location loc = locationLut.get(instruction.get3().get(0).get2());
                XCFA.Process.Procedure.Edge edge = new XCFA.Process.Procedure.Edge(lastLoc, loc, new ArrayList<>());
                procedureBuilder.addEdge(edge);
                return finalLoc; // to ensure no further edges get added
            case 3:
                XCFA.Process.Procedure.Location loc1 = locationLut.get(instruction.get3().get(1).get2());
                XCFA.Process.Procedure.Location loc2 = locationLut.get(instruction.get3().get(2).get2());

                checkState(valueLut.get(instruction.get3().get(0).get2()).getType() instanceof IntType, "Only IntTypes are supported!");
                //noinspection unchecked
                AssumeStmt assume1 = Assume(Neq((Expr<IntType>) valueLut.get(instruction.get3().get(0).get2()), IntLitExpr.of(BigInteger.valueOf(0))));
                //noinspection unchecked
                AssumeStmt assume2 = Assume(Eq((Expr<IntType>) valueLut.get(instruction.get3().get(0).get2()), IntLitExpr.of(BigInteger.valueOf(0))));
                terminatorEdges.put(Tuple2.of(block, loc1.getName()), Tuple3.of(lastLoc, loc1, new ArrayList<>(List.of(assume1))));
                terminatorEdges.put(Tuple2.of(block, loc2.getName()), Tuple3.of(lastLoc, loc2, new ArrayList<>(List.of(assume2))));
                return finalLoc; // to ensure no further edges get added
            default:
                throw new IllegalStateException("Unexpected value: " + instruction.get3().size());
        }
    }

    private static XCFA.Process.Procedure.Location ret(XCFA.Process.Procedure.Builder procedureBuilder, Map<String, Expr<?>> valueLut, XCFA.Process.Procedure.Location finalLoc, Optional<VarDecl<? extends Type>> retVar, XCFA.Process.Procedure.Location lastLoc, Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        List<Stmt> stmts = new ArrayList<>();
        switch(instruction.get3().size()) {
            case 0: break;
            case 1:
                checkState(retVar.isPresent(), "Returning a value from non-void function!");
                Tuple2<Optional<IRType>, String> param = instruction.get3().get(0);
                Optional<IRType> irType = param.get1();
                if(irType.isPresent()) {
                    checkState(createType(irType.get()).equals(retVar.get().getType()));
                    Stmt assignStmt = Assign(retVar.get(), createConstant(irType.get(), param.get2()));
                    stmts.add(assignStmt);
                } else {
                    Expr<?> ref = valueLut.get(param.get2());
                    stmts.add(Assign(retVar.get(), ref));
                }
                break;
            default:
                throw new IllegalStateException("Unexpected value: " + instruction.get3().size());
        }
        XCFA.Process.Procedure.Edge edge = new XCFA.Process.Procedure.Edge(lastLoc, finalLoc, stmts);
        procedureBuilder.addEdge(edge);
        lastLoc = finalLoc;
        return lastLoc;
    }

    private static <T extends Type> Stmt Assign(VarDecl<T> varDecl, Expr<? extends Type> constant) {
        //noinspection unchecked
        return Stmts.Assign(varDecl, (Expr<T>)constant);
    }

}
