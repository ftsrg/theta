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
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntEqExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;
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

        // Handling instructions
        for (String block : locationLut.keySet()) {
            XCFA.Process.Procedure.Location lastLoc = locationLut.get(block);
            Map<String, Expr<?>> valueLut = new HashMap<>();
            Integer[] cnt = new Integer[1]; // to create by-ref passable counter
            for (Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction : ssa.getInstructions(block)) {
                checkState(!(lastLoc.isEndLoc() || lastLoc.isErrorLoc()), "No instruction can occur after a final or error location!");
                switch(instruction.get1()) {
                    case RET:
                        lastLoc = ret(procedureBuilder, localVarLut, finalLoc, retVar, lastLoc, instruction);
                        break;
                    case BR:
                        lastLoc = br(procedureBuilder, localVarLut, locationLut, finalLoc, lastLoc, instruction);
                        break;
                    case SWITCH:
                        lastLoc = sw(procedureBuilder, localVarLut, locationLut, finalLoc, lastLoc, instruction);
                        break;
                    case ADD:
                        break;
                    case SUB:
                        break;
                    case MUL:
                        break;
                    case SDIV:
                        break;
                    case SREM:
                        break;
                    case ALLOCA:
                        break;
                    case LOAD:
                        break;
                    case STORE:
                        break;
                    case FENCE:
                        break;
                    case ICMP:
                        break;
                    case PHI:
                        break;
                    case CALL:
                        break;
                    default:
                        throw new IllegalStateException("Unexpected value: " + instruction.get1());
                }
            }
        }

    }

    private static XCFA.Process.Procedure.Location sw(XCFA.Process.Procedure.Builder procedureBuilder, Map<String, VarDecl<?>> localVarLut, Map<String, XCFA.Process.Procedure.Location> locationLut, XCFA.Process.Procedure.Location finalLoc, XCFA.Process.Procedure.Location lastLoc, Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        checkState(instruction.get3().size() % 2 == 0, "Switch has wrong number of arguments");
        //noinspection unchecked
        Expr<IntType> expr = (Expr<IntType>) localVarLut.get(instruction.get3().get(0).get2()).getRef();
        Expr<BoolType> defaultBranch = null;
        for (int i = 0; i < (instruction.get3().size() / 2) - 1; ++i) {
            XCFA.Process.Procedure.Location loc = locationLut.get(instruction.get3().get(2 + 2*i + 1).get2());
            checkState(localVarLut.get(instruction.get3().get(0).get2()).getType() instanceof IntType, "Only IntTypes are supported!");
            Tuple2<Optional<IRType>, String> param = instruction.get3().get(2 + 2 * i);
            IntEqExpr eq;
            if(param.get1().isPresent()) {
                //noinspection unchecked
                eq = Eq(expr, (Expr<IntType>) createConstant(param.get1().get(), param.get2()));
            } else {
                //noinspection unchecked
                eq = Eq(expr, (Expr<IntType>) localVarLut.get(param.get2()).getRef());
            }
            if(defaultBranch == null) defaultBranch = eq;
            else defaultBranch = BoolExprs.Or(defaultBranch, eq);

            AssumeStmt assume = Assume(eq);
            XCFA.Process.Procedure.Edge edge = new XCFA.Process.Procedure.Edge(lastLoc, loc, List.of(assume));
            procedureBuilder.addEdge(edge);
        }
        XCFA.Process.Procedure.Location loc = locationLut.get(instruction.get3().get(1).get2());
        checkState(localVarLut.get(instruction.get3().get(1).get2()).getType() instanceof IntType, "Only IntTypes are supported!");
        XCFA.Process.Procedure.Edge edge = new XCFA.Process.Procedure.Edge(lastLoc, loc, List.of(Assume(BoolExprs.Not(defaultBranch))));
        procedureBuilder.addEdge(edge);
        return finalLoc; // to ensure no further edges get added
    }

    private static XCFA.Process.Procedure.Location br(XCFA.Process.Procedure.Builder procedureBuilder, Map<String, VarDecl<?>> localVarLut, Map<String, XCFA.Process.Procedure.Location> locationLut, XCFA.Process.Procedure.Location finalLoc, XCFA.Process.Procedure.Location lastLoc, Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        switch(instruction.get3().size()) {
            case 1:
                XCFA.Process.Procedure.Location loc = locationLut.get(instruction.get3().get(0).get2());
                XCFA.Process.Procedure.Edge edge = new XCFA.Process.Procedure.Edge(lastLoc, loc, new ArrayList<>());
                procedureBuilder.addEdge(edge);
                return finalLoc; // to ensure no further edges get added
            case 3:
                XCFA.Process.Procedure.Location loc1 = locationLut.get(instruction.get3().get(1).get2());
                XCFA.Process.Procedure.Location loc2 = locationLut.get(instruction.get3().get(2).get2());

                checkState(localVarLut.get(instruction.get3().get(0).get2()).getType() instanceof IntType, "Only IntTypes are supported!");
                //noinspection unchecked
                AssumeStmt assume1 = Assume(Neq((Expr<IntType>) localVarLut.get(instruction.get3().get(0).get2()).getRef(), IntLitExpr.of(BigInteger.valueOf(0))));
                //noinspection unchecked
                AssumeStmt assume2 = Assume(Eq((Expr<IntType>) localVarLut.get(instruction.get3().get(0).get2()).getRef(), IntLitExpr.of(BigInteger.valueOf(0))));
                XCFA.Process.Procedure.Edge edge1 = new XCFA.Process.Procedure.Edge(lastLoc, loc1, List.of(assume1));
                XCFA.Process.Procedure.Edge edge2 = new XCFA.Process.Procedure.Edge(lastLoc, loc2, List.of(assume2));
                procedureBuilder.addEdge(edge1);
                procedureBuilder.addEdge(edge2);
                return finalLoc; // to ensure no further edges get added
            default:
                throw new IllegalStateException("Unexpected value: " + instruction.get3().size());
        }
    }

    private static XCFA.Process.Procedure.Location ret(XCFA.Process.Procedure.Builder procedureBuilder, Map<String, VarDecl<?>> localVarLut, XCFA.Process.Procedure.Location finalLoc, Optional<VarDecl<? extends Type>> retVar, XCFA.Process.Procedure.Location lastLoc, Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
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
                    RefExpr<?> ref = localVarLut.get(param.get2()).getRef();
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
