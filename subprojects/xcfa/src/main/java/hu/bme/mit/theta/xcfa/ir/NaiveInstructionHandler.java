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
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;

import java.util.*;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.ir.Utils.*;

public class NaiveInstructionHandler implements InstructionHandler{
    private XCFA.Process.Procedure.Location lastLoc;
    private Integer cnt;
    private final Tuple3<String, java.util.Optional<String>, List<Tuple2<String, String>>> function;
    private final XCFA.Process.Procedure.Builder procedureBuilder;
    private final SSAProvider ssa;
    private final Collection<String> processes;
    private final Map<String, VarDecl<?>> localVarLut;
    private final Map<String, Expr<?>> valueLut;
    private final hu.bme.mit.theta.xcfa.XCFA.Process.Procedure.Location finalLoc;
    @SuppressWarnings("OptionalUsedAsFieldOrParameterType")
    private final Optional<VarDecl<? extends Type>> retVar;
    private final Map<String, XCFA.Process.Procedure.Location> locationLut;
    private String block;
    private Map<CallStmt, String> callStmts = new HashMap<>();


    private final Map<Tuple2<String, String>, Tuple3<XCFA.Process.Procedure.Location, XCFA.Process.Procedure.Location, List<Stmt>>> terminatorEdges = new HashMap<>();

    public NaiveInstructionHandler(Tuple3<String, Optional<String>, List<Tuple2<String, String>>> function, XCFA.Process.Procedure.Builder procedureBuilder, SSAProvider ssa, Collection<String> processes, Map<String, VarDecl<?>> localVarLut, XCFA.Process.Procedure.Location finalLoc, Optional<VarDecl<? extends Type>> retVar, Map<String, XCFA.Process.Procedure.Location> locationLut) {
        this.function = function;
        this.procedureBuilder = procedureBuilder;
        this.ssa = ssa;
        this.processes = processes;
        this.localVarLut = localVarLut;
        this.finalLoc = finalLoc;
        this.retVar = retVar;
        this.locationLut = locationLut;
        this.valueLut = new HashMap<>();
    }

    @Override
    public void reinitClass(String block) {
        this.block = block;
        cnt = 0;
        lastLoc = locationLut.get(block);
    }

    private XCFA.Process.Procedure emptyProc(String name) {
        XCFA.Process.Procedure.Builder builder = XCFA.Process.Procedure.builder();
        XCFA.Process.Procedure.Location loc1 = new XCFA.Process.Procedure.Location("loc", null);
        XCFA.Process.Procedure.Location loc2 = new XCFA.Process.Procedure.Location("loc", null);
        builder.addLoc(loc1);
        builder.addLoc(loc2);
        builder.setFinalLoc(loc2);
        builder.setInitLoc(loc1);
        builder.setName(name);
        return builder.build();
    }

    @Override
    public void endProcedure() {
        terminatorEdges.forEach((_obj, edgeTup) -> {
            XCFA.Process.Procedure.Edge edge = new XCFA.Process.Procedure.Edge(edgeTup.get1(), edgeTup.get2(), edgeTup.get3());
            procedureBuilder.addEdge(edge);
        });
    }

    @Override
    public void substituteProcedures(Map<String, XCFA.Process.Procedure> procedures) {
        callStmts.forEach((callStmt, s) -> callStmt.setProcedure(procedures.getOrDefault(s, emptyProc(s))));
    }

    @Override
    public void handleInstruction(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        checkState(!(lastLoc.isEndLoc() || lastLoc.isErrorLoc()), "No instruction can occur after a final or error location!");
        switch(instruction.get1()) {
            case "ret":
                ret(instruction);
                break;
            case "br":
                br(instruction);
                break;
            case "switch":
                sw(instruction);
                break;
            case "add":
                add(instruction);
                break;
            case "sub":
                sub(instruction);
                break;
            case "mul":
                mul(instruction);
                break;
            case "sdiv":
                div(instruction);
                break;
            case "srem":
                rem(instruction);
                break;
            case "alloca":
                alloca(instruction);
                break;
            case "load":
                load(instruction);
                break;
            case "store":
                store(instruction);
                break;
            case "icmp":
                cmp(instruction);
                break;
            case "phi":
                phi(instruction);
                break;
            case "call":
                call(instruction);
                break;
            case "zext":
                load(instruction);
                break;
            default:
                throw new IllegalStateException("Unexpected value: " + instruction.get1());
        }
    }

    private void call(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        XCFA.Process.Procedure.Location newLoc = new XCFA.Process.Procedure.Location(block + "_" + cnt++, new HashMap<>());
        String funcName = instruction.get3().get(paramSize - 1).get2();
        VarDecl<?> callVar = null;
        if(instruction.get2().isPresent()) {
            callVar = createVariable(block +"_"+ cnt++, instruction.get2().get().get1());
            procedureBuilder.getLocalVars().put(callVar, Optional.empty());
            localVarLut.put(callVar.getName(), callVar);
            localVarLut.put(instruction.get2().get().get2(), callVar);
            valueLut.put(instruction.get2().get().get2(), callVar.getRef());
        }
        List<Expr<?>> exprs = new ArrayList<>();
        for(int i = 0 ; i < paramSize - 1; ++i) {
            Expr<? extends Type> expr = getExpr(instruction, i);
            if(expr != null) exprs.add(expr);
        }
        CallStmt stmt = new CallStmt(callVar, null, exprs);
        callStmts.put(stmt, funcName);
        XCFA.Process.Procedure.Edge edge = new XCFA.Process.Procedure.Edge(lastLoc, newLoc, List.of(stmt));
        procedureBuilder.addLoc(newLoc);
        procedureBuilder.addEdge(edge);
        lastLoc = newLoc;
    }

    /*
     * var = phi [expr label]*
     */
    private void phi(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        checkState(instruction.get3().size() % 2 == 0, "Phi node should have an even number of arguments");
        checkState(instruction.get2().isPresent(), "Return var must be present!");
        VarDecl<?> phiVar = createVariable(block +"_"+ cnt++, instruction.get2().get().get1());
        procedureBuilder.getLocalVars().put(phiVar, Optional.empty());
        localVarLut.put(phiVar.getName(), phiVar);
        localVarLut.put(instruction.get2().get().get2(), phiVar);
        valueLut.put(instruction.get2().get().get2(), phiVar.getRef());
        for(int i = 0; i < (instruction.get3().size()) / 2; ++i) {
            String blockName = instruction.get3().get(2*i + 1).get2();
            Expr<?> value = getExpr(instruction, 2*i );
            Tuple2<String, String> key = Tuple2.of(blockName, block);
            Tuple3<XCFA.Process.Procedure.Location, XCFA.Process.Procedure.Location, List<Stmt>> val = terminatorEdges.getOrDefault(key, Tuple3.of(new XCFA.Process.Procedure.Location(key.get1(), null), new XCFA.Process.Procedure.Location(key.get2(), null), new ArrayList<>()));
            val.get3().add(Assign(phiVar, value));
            terminatorEdges.put(key, val);
        }
    }

    /*
     * var = cmp expr expr
     */
    private void cmp(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<?> lhsExpr = getExpr(instruction, paramSize - 2);
        Expr<?> rhsExpr = getExpr(instruction, paramSize - 1);

        checkState(lhsExpr.getType() == IntType.getInstance(), "Cmp must compare integer types!");
        checkState(rhsExpr.getType() == IntType.getInstance(), "Cmp must compare integer types!");

        //noinspection unchecked
        Expr<IntType> lhs = (Expr<IntType>) lhsExpr;
        //noinspection unchecked
        Expr<IntType> rhs = (Expr<IntType>) rhsExpr;

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


    /*
     * store expr expr
     */
    private void store(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        checkState(paramSize == 2, "Store should have two arguments");
        String lhs = instruction.get3().get(0).get2();
        String rhs = instruction.get3().get(1).get2();
        if(localVarLut.containsKey(lhs) && !valueLut.containsKey(lhs)) { // function param
            procedureBuilder.getLocalVars().remove(localVarLut.get(rhs));
            localVarLut.put(rhs, localVarLut.get(lhs));
            valueLut.put(rhs, localVarLut.get(lhs).getRef());
            valueLut.put(lhs, localVarLut.get(lhs).getRef());
        } else {
            XCFA.Process.Procedure.Location loc = new XCFA.Process.Procedure.Location(block + "_" + cnt++, new HashMap<>());
            Stmt stmt = Assign(localVarLut.get(instruction.get3().get(1).get2()), getExpr(instruction, 0));
            XCFA.Process.Procedure.Edge edge = new XCFA.Process.Procedure.Edge(lastLoc, loc, List.of(stmt));
            procedureBuilder.addLoc(loc);
            procedureBuilder.addEdge(edge);
            lastLoc = loc;
        }
    }

    /*
     * var = load expr
     */
    private void load(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        checkState(instruction.get2().isPresent(), "Load must load into a variable");
        valueLut.put(instruction.get2().get().get2(), localVarLut.get(instruction.get3().get(0).get2()).getRef());
    }

    /*
     * var = alloca
     */
    private void alloca(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        checkState(instruction.get2().isPresent(), "Alloca must have a variable tied to it");
        VarDecl<?> var = createVariable(instruction.get2().get().get2(), instruction.get2().get().get1());
        procedureBuilder.getLocalVars().put(var, Optional.empty());
        localVarLut.put(instruction.get2().get().get2(), var);
        valueLut.put(instruction.get2().get().get2(), var.getRef());
    }

    /*
     * var = rem expr expr
     * var : int
     * expr : int
     */
    private void rem(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<?> lhs = getExpr(instruction, paramSize - 2);
        Expr<?> rhs = getExpr(instruction, paramSize - 1);

        checkState(lhs.getType() == IntType.getInstance(), "Rem only supports integer types!");
        checkState(rhs.getType() == IntType.getInstance(), "Rem only supports integer types!");
        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        //noinspection unchecked
        valueLut.put(instruction.get2().get().get2(), Rem((Expr<IntType>) lhs, (Expr<IntType>) rhs));
    }

    /*
     * var = div expr expr
     * var : int
     * expr : int
     */
    private void div(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<?> lhs = getExpr(instruction, paramSize - 2);
        Expr<?> rhs = getExpr(instruction, paramSize - 1);

        checkState(lhs.getType() == IntType.getInstance(), "Div only supports integer types!");
        checkState(rhs.getType() == IntType.getInstance(), "Div only supports integer types!");
        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        //noinspection unchecked
        valueLut.put(instruction.get2().get().get2(), Div((Expr<IntType>) lhs, (Expr<IntType>) rhs));
    }

    /*
     * var = mul expr expr
     * var : int
     * expr : int
     */
    private void mul(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<?> lhs = getExpr(instruction, paramSize - 2);
        Expr<?> rhs = getExpr(instruction, paramSize - 1);

        checkState(lhs.getType() == IntType.getInstance(), "Mul only supports integer types!");
        checkState(rhs.getType() == IntType.getInstance(), "Mul only supports integer types!");
        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        //noinspection unchecked
        valueLut.put(instruction.get2().get().get2(), Mul((Expr<IntType>) lhs, (Expr<IntType>) rhs));
    }

    /*
     * var = sub expr expr
     * var : int
     * expr : int
     */
    private void sub(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<?> lhs = getExpr(instruction, paramSize - 2);
        Expr<?> rhs = getExpr(instruction, paramSize - 1);

        checkState(lhs.getType() == IntType.getInstance(), "Sub only supports integer types!");
        checkState(rhs.getType() == IntType.getInstance(), "Sub only supports integer types!");
        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        //noinspection unchecked
        valueLut.put(instruction.get2().get().get2(), Sub((Expr<IntType>) lhs, (Expr<IntType>) rhs));
    }

    /*
     * var = add expr expr
     * var : int
     * expr : int
     */
    private void add(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<?> lhs = getExpr(instruction, paramSize - 2);
        Expr<?> rhs = getExpr(instruction, paramSize - 1);

        checkState(lhs.getType() == IntType.getInstance(), "Add only supports integer types!");
        checkState(rhs.getType() == IntType.getInstance(), "Add only supports integer types!");
        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        //noinspection unchecked
        valueLut.put(instruction.get2().get().get2(), Add((Expr<IntType>) lhs, (Expr<IntType>) rhs));
    }

    /*
     * sw var label [const label]*
     * TODO: 3rd param?
     * var: int
     * const: int
     */
    private void sw(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        checkState(instruction.get3().size() % 2 == 0, "Switch has wrong number of arguments");
        Expr<?> varExpr = getExpr(instruction, 0);
        checkState(varExpr.getType() == IntType.getInstance(), "Var has to be an integer!");
        //noinspection unchecked
        Expr<IntType> var = (Expr<IntType>) varExpr;
        Expr<BoolType> defaultBranch = null;
        for (int i = 0; i < (instruction.get3().size() / 2) - 1; ++i) {
            XCFA.Process.Procedure.Location loc = locationLut.get(instruction.get3().get(2 + 2*i + 1).get2());
            Expr<?> constExpr = getExpr(instruction, 2 + 2 * i);
            checkState(constExpr.getType() == IntType.getInstance(), "Constant has to be an integer!");
            //noinspection unchecked
            IntEqExpr eq = Eq(var, (Expr<IntType>) constExpr);
            if(defaultBranch == null) defaultBranch = eq;
            else defaultBranch = BoolExprs.Or(defaultBranch, eq);
            AssumeStmt assume = Assume(eq);
            Tuple2<String, String> key = Tuple2.of(block, loc.getName());
            List<Stmt> stmts = terminatorEdges.getOrDefault(key, Tuple3.of(lastLoc, loc, new ArrayList<>())).get3();
            stmts.add(assume);
            terminatorEdges.put(key, Tuple3.of(lastLoc, loc, stmts));
        }
        XCFA.Process.Procedure.Location loc = locationLut.get(instruction.get3().get(1).get2());
        XCFA.Process.Procedure.Edge edge = new XCFA.Process.Procedure.Edge(lastLoc, loc, List.of(Assume(BoolExprs.Not(defaultBranch))));
        procedureBuilder.addEdge(edge);
        lastLoc = finalLoc;
    }

    /*
     * br label;
     * br expr label label;
     */
    private void br(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        switch(instruction.get3().size()) {
            case 1:
                XCFA.Process.Procedure.Location loc = locationLut.get(instruction.get3().get(0).get2());
                Tuple2<String, String> key = Tuple2.of(block, loc.getName());
                List<Stmt> stmts = terminatorEdges.getOrDefault(key, Tuple3.of(lastLoc, loc, new ArrayList<>())).get3();
                terminatorEdges.put(key, Tuple3.of(lastLoc, loc, stmts));
                break;
            case 3:
                XCFA.Process.Procedure.Location loc1 = locationLut.get(instruction.get3().get(1).get2());
                XCFA.Process.Procedure.Location loc2 = locationLut.get(instruction.get3().get(2).get2());

                Expr<?> lhs = getExpr(instruction, 0);
                Expr<?> rhs = createConstant("i32 0");
                boolean lhsType = lhs.getType() == IntType.getInstance() || lhs.getType() == BoolType.getInstance();
                boolean rhsType = rhs.getType() == IntType.getInstance() || rhs.getType() == BoolType.getInstance();
                checkState(lhsType && rhsType, "Both expressions should be int or bool types!");
                //noinspection unchecked                XCFA.Process.Procedure.Edge edge = new XCFA.Process.Procedure.Edge(lastLoc, loc, new ArrayList<>());

                AssumeStmt assume1 = Assume(Neq((Expr<IntType>) lhs, (Expr<IntType>) rhs));
                //noinspection unchecked
                AssumeStmt assume2 = Assume(Eq((Expr<IntType>) lhs, (Expr<IntType>) rhs));
                key = Tuple2.of(block, loc1.getName());
                stmts = terminatorEdges.getOrDefault(key, Tuple3.of(lastLoc, loc1, new ArrayList<>())).get3();
                stmts.add(assume1);
                terminatorEdges.put(key, Tuple3.of(lastLoc, loc1, stmts));
                key = Tuple2.of(block, loc2.getName());
                stmts = terminatorEdges.getOrDefault(key, Tuple3.of(lastLoc, loc1, new ArrayList<>())).get3();
                stmts.add(assume2);
                terminatorEdges.put(key, Tuple3.of(lastLoc, loc2, stmts));
                break;
            default:
                throw new IllegalStateException("Unexpected value: " + instruction.get3().size());
        }
        lastLoc = finalLoc;
    }

    /*
     * ret;
     * ret expr;
     */
    private void ret(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        List<Stmt> stmts = new ArrayList<>();
        switch(instruction.get3().size()) {
            case 0: checkState(retVar.isEmpty(), "Not returning a value from non-void function!"); break;
            case 1:
                checkState(retVar.isPresent(), "Returning a value from void function!");
                Stmt assignStmt = Assign(retVar.get(), cast(getExpr(instruction, 0), retVar.get().getType()));
                stmts.add(assignStmt);
                break;
            default:
                throw new IllegalStateException("Unexpected value: " + instruction.get3().size());
        }
        XCFA.Process.Procedure.Edge edge = new XCFA.Process.Procedure.Edge(lastLoc, finalLoc, stmts);
        procedureBuilder.addEdge(edge);
        lastLoc = finalLoc;
    }

    private <T extends Type> Stmt Assign(VarDecl<T> varDecl, Expr<? extends Type> expr) {
        boolean lhsOk = varDecl.getType() == IntType.getInstance() || varDecl.getType() == BoolType.getInstance();
        boolean rhsOk = expr.getType() == IntType.getInstance() || expr.getType() == BoolType.getInstance();
        checkState(lhsOk && rhsOk, "Cannot assign different types of expressions!");
        //noinspection unchecked
        return Stmts.Assign((VarDecl<IntType>) varDecl, (Expr<IntType>) expr);
    }

    private Expr<? extends Type> getExpr(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction, int i) {
        Expr<? extends Type> expr;
        Tuple2<Optional<String>, String> param1 = instruction.get3().get(i);
        if (param1.get1().isEmpty()) {
            expr = createConstant(param1.get2());
        } else {
            expr = valueLut.get(param1.get2());
        }
        return expr;
    }

}
