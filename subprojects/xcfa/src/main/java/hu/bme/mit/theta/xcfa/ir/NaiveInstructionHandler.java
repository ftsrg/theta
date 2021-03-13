package hu.bme.mit.theta.xcfa.ir;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.common.Tuple4;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntEqExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.xcfa.XCFA;

import java.math.BigInteger;
import java.util.*;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.xcfa.ir.Utils.*;

public class NaiveInstructionHandler implements InstructionHandler{
    private XCFA.Process.Procedure.Location lastLoc;
    private Map<String, Expr<?>> valueLut;
    private Integer cnt;
    private final Tuple3<String, java.util.Optional<IRType>, List<Tuple2<IRType, String>>> function;
    private final XCFA.Process.Procedure.Builder procedureBuilder;
    private final SSAProvider ssa;
    private final Collection<String> processes;
    private final Map<String, VarDecl<?>> localVarLut;
    private final hu.bme.mit.theta.xcfa.XCFA.Process.Procedure.Location finalLoc;
    @SuppressWarnings("OptionalUsedAsFieldOrParameterType")
    private final Optional<VarDecl<? extends Type>> retVar;
    private final Map<String, XCFA.Process.Procedure.Location> locationLut;
    private String block;


    private Map<Tuple2<String, String>, Tuple3<XCFA.Process.Procedure.Location, XCFA.Process.Procedure.Location, List<Stmt>>> terminatorEdges = new HashMap<>();

    public NaiveInstructionHandler(Tuple3<String, Optional<IRType>, List<Tuple2<IRType, String>>> function, XCFA.Process.Procedure.Builder procedureBuilder, SSAProvider ssa, Collection<String> processes, Map<String, VarDecl<?>> localVarLut, XCFA.Process.Procedure.Location finalLoc, Optional<VarDecl<? extends Type>> retVar, Map<String, XCFA.Process.Procedure.Location> locationLut) {
        this.function = function;
        this.procedureBuilder = procedureBuilder;
        this.ssa = ssa;
        this.processes = processes;
        this.localVarLut = localVarLut;
        this.finalLoc = finalLoc;
        this.retVar = retVar;
        this.locationLut = locationLut;
    }

    @Override
    public void reinitClass(String block) {
        this.block = block;
        valueLut = new HashMap<>();
        cnt = 0;
        lastLoc = locationLut.get(block);
    }

    @Override
    public void handleInstruction(Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        checkState(!(lastLoc.isEndLoc() || lastLoc.isErrorLoc()), "No instruction can occur after a final or error location!");
        switch(instruction.get1()) {
            case RET:
                ret(instruction);
                break;
            case BR:
                br(instruction);
                break;
            case SWITCH:
                sw(instruction);
                break;
            case ADD:
                add(instruction);
                break;
            case SUB:
                sub(instruction);
                break;
            case MUL:
                mul(instruction);
                break;
            case SDIV:
                div(instruction);
                break;
            case SREM:
                rem(instruction);
                break;
            case ALLOCA:
                alloca(instruction);
                break;
            case LOAD:
                load(instruction);
                break;
            case STORE:
                store(instruction);
                break;
            case ICMP:
                cmp(valueLut, instruction);
                break;
            case PHI:
                phi(instruction);
                break;
            case CALL:
                call(instruction);
                break;
            default:
                throw new IllegalStateException("Unexpected value: " + instruction.get1());
        }
    }


    private void call(Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        String funcName = instruction.get3().get(paramSize - 2).get2();
        // TODO
    }

    private void phi(Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        checkState(instruction.get3().size() % 2 == 1, "Phi node should have an odd number of arguments");
        checkState(instruction.get3().get(0).get1().isPresent(), "Return type must be present in phi node!");
        VarDecl<?> phiVar = createVariable(block +"_"+ cnt++, instruction.get3().get(0).get1().get());
        procedureBuilder.getLocalVars().put(phiVar, null);
        localVarLut.put(phiVar.getName(), phiVar);
        for(int i = 0; i < (instruction.get3().size() + 1) / 2; ++i) {
            String blockName = instruction.get3().get(2*i + 1).get2();
            Expr<?> value = getExpr(instruction, 2*i + 2);
            checkState(terminatorEdges.containsKey(Tuple2.of(block, blockName)), "Edge does not exist!");
            terminatorEdges.get(Tuple2.of(block, blockName)).get3().add(Assign(phiVar, value));
        }
    }


    private void cmp(Map<String, Expr<?>> valueLut, Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<IntType> lhs = getExpr(instruction, paramSize - 2);
        Expr<IntType> rhs = getExpr(instruction, paramSize - 1);

        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        switch(instruction.get3().get(0).get2()) {
            case "eq": valueLut.put(instruction.get2().get().get2(), Eq(lhs, rhs)); break;
            case "ne": valueLut.put(instruction.get2().get().get2(), Neq(lhs, rhs)); break;
            case "ugt": case "sgt": valueLut.put(instruction.get2().get().get2(), Gt(lhs, rhs)); break;
            case "uge": case "sge": valueLut.put(instruction.get2().get().get2(), Geq(lhs, rhs)); break;
            case "ult": case "slt": valueLut.put(instruction.get2().get().get2(), Lt(lhs, rhs)); break;
            case "ule": case "sle": valueLut.put(instruction.get2().get().get2(), Leq(lhs, rhs)); break;
            default:
                throw new IllegalStateException("Unexpected value: " + instruction.get3().get(0).get2());
        }

    }


    private void store(Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        checkState(paramSize == 2, "Store should have two arguments");
        XCFA.Process.Procedure.Location loc = new XCFA.Process.Procedure.Location(block + "_" + cnt++, new HashMap<>());
        Stmt stmt = Assign(localVarLut.get(instruction.get3().get(0).get2()), getExpr(instruction, paramSize - 1));
        XCFA.Process.Procedure.Edge edge = new XCFA.Process.Procedure.Edge(lastLoc, loc, List.of(stmt));
        procedureBuilder.addLoc(loc);
        procedureBuilder.addEdge(edge);
        lastLoc = loc;
    }

    private void load(Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        checkState(instruction.get3().size() >= 2);
        checkState(instruction.get2().isPresent(), "Load must load into a variable");
        valueLut.put(instruction.get2().get().get2(), localVarLut.get(instruction.get3().get(1).get2()).getRef());
    }

    private void alloca(Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        checkState(instruction.get2().isPresent(), "Alloca must have a variable tied to it");
        VarDecl<?> var = createVariable(instruction.get2().get().get2(), IRType.INTEGER32);
        procedureBuilder.getLocalVars().put(var, null);
        localVarLut.put(instruction.get2().get().get2(), var);
    }

    private void rem(Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<IntType> lhs = getExpr(instruction, paramSize - 2);
        Expr<IntType> rhs = getExpr(instruction, paramSize - 1);

        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        valueLut.put(instruction.get2().get().get2(), Rem(lhs, rhs));
    }

    private void div(Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<IntType> lhs = getExpr(instruction, paramSize - 2);
        Expr<IntType> rhs = getExpr(instruction, paramSize - 1);

        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        valueLut.put(instruction.get2().get().get2(), Div(lhs, rhs));
    }

    private void mul(Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<IntType> lhs = getExpr(instruction, paramSize - 2);
        Expr<IntType> rhs = getExpr(instruction, paramSize - 1);

        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        valueLut.put(instruction.get2().get().get2(), Mul(lhs, rhs));
    }

    private void sub(Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<IntType> lhs = getExpr(instruction, paramSize - 2);
        Expr<IntType> rhs = getExpr(instruction, paramSize - 1);

        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        valueLut.put(instruction.get2().get().get2(), Sub(lhs, rhs));
    }

    private void add(Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<IntType> lhs = getExpr(instruction, paramSize - 2);
        Expr<IntType> rhs = getExpr(instruction, paramSize - 1);

        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        valueLut.put(instruction.get2().get().get2(), Add(lhs, rhs));
    }

    private Expr<IntType> getExpr(Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction, int i) {
        Expr<IntType> expr;
        Tuple2<Optional<IRType>, String> param1 = instruction.get3().get(i);
        if (param1.get1().isEmpty()) {
            //noinspection unchecked
            expr = (Expr<IntType>) createConstant(param1.get2());
        } else {
            //noinspection unchecked
            expr = (Expr<IntType>) valueLut.get(param1.get2());
        }
        return expr;
    }

    private void sw(Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        checkState(instruction.get3().size() % 2 == 0, "Switch has wrong number of arguments");
        //noinspection unchecked
        Expr<IntType> expr = (Expr<IntType>) valueLut.get(instruction.get3().get(0).get2());
        Expr<BoolType> defaultBranch = null;
        for (int i = 0; i < (instruction.get3().size() / 2) - 1; ++i) {
            XCFA.Process.Procedure.Location loc = locationLut.get(instruction.get3().get(2 + 2*i + 1).get2());
            checkState(valueLut.get(instruction.get3().get(0).get2()).getType() instanceof IntType, "Only IntTypes are supported!");
            IntEqExpr eq = Eq(expr, getExpr(instruction, 2 + 2 * i));
            if(defaultBranch == null) defaultBranch = eq;
            else defaultBranch = BoolExprs.Or(defaultBranch, eq);
            AssumeStmt assume = Assume(eq);
            terminatorEdges.put(Tuple2.of(block, loc.getName()), Tuple3.of(lastLoc, loc, new ArrayList<>(List.of(assume))));
        }
        XCFA.Process.Procedure.Location loc = locationLut.get(instruction.get3().get(1).get2());
        checkState(valueLut.get(instruction.get3().get(1).get2()).getType() instanceof IntType, "Only IntTypes are supported!");
        XCFA.Process.Procedure.Edge edge = new XCFA.Process.Procedure.Edge(lastLoc, loc, List.of(Assume(BoolExprs.Not(defaultBranch))));
        procedureBuilder.addEdge(edge);
        lastLoc = finalLoc;
    }

    private void br(Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        switch(instruction.get3().size()) {
            case 1:
                XCFA.Process.Procedure.Location loc = locationLut.get(instruction.get3().get(0).get2());
                XCFA.Process.Procedure.Edge edge = new XCFA.Process.Procedure.Edge(lastLoc, loc, new ArrayList<>());
                procedureBuilder.addEdge(edge);
                break;
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
                break;
            default:
                throw new IllegalStateException("Unexpected value: " + instruction.get3().size());
        }
        lastLoc = finalLoc;
    }

    private void ret(Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction) {
        List<Stmt> stmts = new ArrayList<>();
        switch(instruction.get3().size()) {
            case 0: break;
            case 1:
                checkState(retVar.isPresent(), "Returning a value from non-void function!");
                Stmt assignStmt = Assign(retVar.get(), getExpr(instruction, 0));
                stmts.add(assignStmt);
                break;
            default:
                throw new IllegalStateException("Unexpected value: " + instruction.get3().size());
        }
        XCFA.Process.Procedure.Edge edge = new XCFA.Process.Procedure.Edge(lastLoc, finalLoc, stmts);
        procedureBuilder.addEdge(edge);
        lastLoc = finalLoc;
    }

    private static <T extends Type> Stmt Assign(VarDecl<T> varDecl, Expr<? extends Type> constant) {
        //noinspection unchecked
        return Stmts.Assign(varDecl, (Expr<T>)constant);
    }


}
