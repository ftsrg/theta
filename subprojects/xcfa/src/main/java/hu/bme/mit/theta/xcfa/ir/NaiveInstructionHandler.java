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
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntEqExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;

import java.util.*;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.ir.Utils.*;

public class NaiveInstructionHandler implements InstructionHandler{
    private final Collection<Tuple3<String, Optional<String>, List<Tuple2<String, String>>>> functions;
    private XcfaLocation lastLoc;
    private Integer cnt;
    private final Tuple3<String, java.util.Optional<String>, List<Tuple2<String, String>>> function;
    private final XcfaProcedure.Builder procedureBuilder;
    private final SSAProvider ssa;
    private final Collection<String> processes;
    private final Map<String, VarDecl<?>> localVarLut;
    private final Map<String, Expr<?>> valueLut;
    private final Set<String> ptrs;
    private final XcfaLocation finalLoc;
    @SuppressWarnings("OptionalUsedAsFieldOrParameterType")
    private final Optional<VarDecl<? extends Type>> retVar;
    private final Map<String, XcfaLocation> locationLut;
    private String block;
    private Map<CallStmt, String> callStmts = new HashMap<>();


    private final Map<Tuple2<String, String>, Tuple3<XcfaLocation, XcfaLocation, List<Stmt>>> terminatorEdges = new HashMap<>();

    public NaiveInstructionHandler(Collection<Tuple3<String, Optional<String>, List<Tuple2<String, String>>>> functions, Tuple3<String, Optional<String>, List<Tuple2<String, String>>> function, XcfaProcedure.Builder procedureBuilder, SSAProvider ssa, Collection<String> processes, Map<String, VarDecl<?>> localVarLut, XcfaLocation finalLoc, Optional<VarDecl<? extends Type>> retVar, Map<String, XcfaLocation> locationLut) {
        this.functions = functions;
        this.function = function;
        this.procedureBuilder = procedureBuilder;
        this.ssa = ssa;
        this.processes = processes;
        this.localVarLut = localVarLut;
        this.finalLoc = finalLoc;
        this.retVar = retVar;
        this.locationLut = locationLut;
        this.valueLut = new HashMap<>();
        this.ptrs = new HashSet<>();
        localVarLut.forEach((s, varDecl) -> valueLut.put(s, varDecl.getRef()));
    }

    @Override
    public void reinitClass(String block) {
        this.block = block;
        cnt = 0;
        lastLoc = locationLut.get(block);
    }

    private XcfaProcedure emptyProc(String name) {
        XcfaProcedure.Builder builder = XcfaProcedure.builder();
        XcfaLocation loc1 = new XcfaLocation("loc", null);
        XcfaLocation loc2 = new XcfaLocation("loc", null);
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
            XcfaEdge edge = new XcfaEdge(edgeTup.get1(), edgeTup.get2(), edgeTup.get3());
            procedureBuilder.addEdge(edge);
        });
    }

    @Override
    public void substituteProcedures(Map<String, XcfaProcedure> procedures) {
        callStmts.forEach((callStmt, s) -> callStmt.setProcedure(procedures.getOrDefault(s, emptyProc(s))));
    }

    private int instrCnt = 0;

    @Override
    public void handleInstruction(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        checkState(!(lastLoc.isEndLoc() || lastLoc.isErrorLoc()), "No instruction can occur after a final or error location!");
        try {
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
                case "and":
                    and(instruction);
                    break;
                case "or":
                    or(instruction);
                    break;
                case "xor":
                    xor(instruction);
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
                case "select":
                    select(instruction);
                    break;
                case "bitcast":
                case "zext":
                    load(instruction);
                    break;
                case "unreachable":
                    break;
                default:
                    throw new IllegalStateException("Unexpected value: " + instruction.get1());
            }
            instrCnt++;
        } catch (Throwable throwable) {
            System.err.println("Error with instruction #" + instrCnt + ": " + instruction.toString());
            throwable.printStackTrace();
        }
    }

    private void call(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        String funcName = instruction.get3().get(paramSize - 1).get2();

        if(functions.stream().anyMatch(objects -> objects.get1().equals(funcName) && objects.get3().size() == paramSize-1)) { // known function
            XcfaLocation newLoc = new XcfaLocation(block + "_" + cnt++, new HashMap<>());

            VarDecl<?> callVar = null;
            if (instruction.get2().isPresent()) {
                callVar = createVariable(block + "_" + cnt++, instruction.get2().get().get1());
                procedureBuilder.getLocalVars().put(callVar, Optional.empty());
                localVarLut.put(callVar.getName(), callVar);
                localVarLut.put(instruction.get2().get().get2(), callVar);
                valueLut.put(instruction.get2().get().get2(), callVar.getRef());
            }
            List<Expr<?>> exprs = new ArrayList<>();
            for (int i = 0; i < paramSize - 1; ++i) {
                Expr<? extends Type> expr = getExpr(instruction, i);
                if (expr != null) exprs.add(expr);
            }
            CallStmt stmt = new CallStmt(callVar, null, exprs);
            callStmts.put(stmt, funcName);
            XcfaEdge edge = new XcfaEdge(lastLoc, newLoc, List.of(stmt));
            procedureBuilder.addLoc(newLoc);
            procedureBuilder.addEdge(edge);
            lastLoc = newLoc;
        } else {
            if(instruction.get2().isPresent()) { // assigning the value
                VarDecl<?> callVar = createVariable(block +"_"+ cnt++, instruction.get2().get().get1());
                procedureBuilder.getLocalVars().put(callVar, Optional.empty());
                localVarLut.put(callVar.getName(), callVar);
                localVarLut.put(instruction.get2().get().get2(), callVar);
                valueLut.put(instruction.get2().get().get2(), callVar.getRef());
                XcfaLocation newLoc = new XcfaLocation(block + "_" + cnt++, new HashMap<>());
                XcfaEdge edge = new XcfaEdge(lastLoc, newLoc, List.of(Havoc(callVar)));
                procedureBuilder.addLoc(newLoc);
                procedureBuilder.addEdge(edge);
                lastLoc = newLoc;
            }
            for (int i = 0; i < instruction.get3().size(); ++i) {   // using a pointer
                if(localVarLut.containsKey(instruction.get3().get(i).get2())) {
                    Expr<?> expr = getExpr(instruction, i);
                    if (expr instanceof RefExpr<?> && ((RefExpr<?>) expr).getDecl() instanceof VarDecl<?>) {
                        XcfaLocation newLoc = new XcfaLocation(block + "_" + cnt++, new HashMap<>());
                        XcfaEdge edge = new XcfaEdge(lastLoc, newLoc, List.of(Havoc((VarDecl<?>) ((RefExpr<?>) expr).getDecl())));
                        procedureBuilder.addLoc(newLoc);
                        procedureBuilder.addEdge(edge);
                        lastLoc = newLoc;
                    }
                }
            }

        }
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
            Tuple3<XcfaLocation, XcfaLocation, List<Stmt>> val = terminatorEdges.getOrDefault(key, Tuple3.of(new XcfaLocation(key.get1(), null), new XcfaLocation(key.get2(), null), new ArrayList<>()));
            val.get3().add(Assign(phiVar, value));
            terminatorEdges.put(key, val);
        }
    }

    /*
     * var = select cond expr expr
     * var : int
     * expr : int
     */
    private void select(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<?> cond = getExpr(instruction, paramSize - 3);
        Expr<?> lhs = getExpr(instruction, paramSize - 2);
        Expr<?> rhs = getExpr(instruction, paramSize - 1);

        checkState(cond.getType() == BoolType.getInstance(), "Select cond only supports boolean types!");
        checkState(lhs.getType() == IntType.getInstance(), "Select arg only supports integer types!");
        checkState(rhs.getType() == IntType.getInstance(), "Select arg only supports integer types!");
        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        //noinspection unchecked
        valueLut.put(instruction.get2().get().get2(), Ite((Expr<BoolType>) cond, (Expr<IntType>) lhs, (Expr<IntType>) rhs));
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
            XcfaLocation loc = new XcfaLocation(block + "_" + cnt++, new HashMap<>());
            Stmt stmt = Assign(localVarLut.get(instruction.get3().get(1).get2()), getExpr(instruction, 0));
            XcfaEdge edge = new XcfaEdge(lastLoc, loc, List.of(stmt));
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
     * var = xor expr expr
     * var : int
     * expr : int
     */
    private void xor(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<?> lhs = getExpr(instruction, paramSize - 2);
        if(lhs.getType() == IntType.getInstance()) {
            //noinspection unchecked
            lhs = Neq((Expr<IntType>) lhs, (Expr<IntType>) createConstant("i1 0"));
        }
        Expr<?> rhs = getExpr(instruction, paramSize - 1);
        if(rhs.getType() == IntType.getInstance()) {
            //noinspection unchecked
            rhs = Neq((Expr<IntType>) rhs, (Expr<IntType>) createConstant("i1 0"));
        }
        checkState(lhs.getType() == BoolType.getInstance(), "And only supports boolean types!");
        checkState(rhs.getType() == BoolType.getInstance(), "And only supports boolean types!");
        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        //noinspection unchecked
        valueLut.put(instruction.get2().get().get2(), BoolExprs.Xor((Expr<BoolType>) lhs, (Expr<BoolType>) rhs));
    }
    /*
     * var = and expr expr
     * var : int
     * expr : int
     */
    private void and(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<?> lhs = getExpr(instruction, paramSize - 2);
        if(lhs.getType() == IntType.getInstance()) {
            //noinspection unchecked
            lhs = Neq((Expr<IntType>) lhs, (Expr<IntType>) createConstant("i1 0"));
        }
        Expr<?> rhs = getExpr(instruction, paramSize - 1);
        if(rhs.getType() == IntType.getInstance()) {
            //noinspection unchecked
            rhs = Neq((Expr<IntType>) rhs, (Expr<IntType>) createConstant("i1 0"));
        }
        checkState(lhs.getType() == BoolType.getInstance(), "And only supports boolean types!");
        checkState(rhs.getType() == BoolType.getInstance(), "And only supports boolean types!");
        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        //noinspection unchecked
        valueLut.put(instruction.get2().get().get2(), BoolExprs.And((Expr<BoolType>) lhs, (Expr<BoolType>) rhs));
    }


    /*
     * var = or expr expr
     * var : int
     * expr : int
     */
    private void or(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction) {
        int paramSize = instruction.get3().size();
        Expr<?> lhs = getExpr(instruction, paramSize - 2);
        if(lhs.getType() == IntType.getInstance()) {
            //noinspection unchecked
            lhs = Neq((Expr<IntType>) lhs, (Expr<IntType>) createConstant("i1 0"));
        }
        Expr<?> rhs = getExpr(instruction, paramSize - 1);
        if(rhs.getType() == IntType.getInstance()) {
            //noinspection unchecked
            rhs = Neq((Expr<IntType>) rhs, (Expr<IntType>) createConstant("i1 0"));
        }


        checkState(lhs.getType() == BoolType.getInstance(), "Or only supports boolean types!");
        checkState(rhs.getType() == BoolType.getInstance(), "Or only supports boolean types!");
        checkState(instruction.get2().isPresent(), "Instruction must have return variable");
        //noinspection unchecked
        valueLut.put(instruction.get2().get().get2(), Or((Expr<BoolType>) lhs, (Expr<BoolType>) rhs));
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
            XcfaLocation loc = locationLut.get(instruction.get3().get(2 + 2*i + 1).get2());
            Expr<?> constExpr = getExpr(instruction, 2 + 2 * i);
            checkState(constExpr.getType() == IntType.getInstance(), "Constant has to be an integer!");
            //noinspection unchecked
            IntEqExpr eq = Eq(var, (Expr<IntType>) constExpr);
            if(defaultBranch == null) defaultBranch = eq;
            else defaultBranch = Or(defaultBranch, eq);
            AssumeStmt assume = Assume(eq);
            Tuple2<String, String> key = Tuple2.of(block, loc.getName());
            List<Stmt> stmts = terminatorEdges.getOrDefault(key, Tuple3.of(lastLoc, loc, new ArrayList<>())).get3();
            stmts.add(assume);
            terminatorEdges.put(key, Tuple3.of(lastLoc, loc, stmts));
        }
        XcfaLocation loc = locationLut.get(instruction.get3().get(1).get2());
        XcfaEdge edge = new XcfaEdge(lastLoc, loc, List.of(Assume(BoolExprs.Not(defaultBranch))));
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
                XcfaLocation loc = locationLut.get(instruction.get3().get(0).get2());
                Tuple2<String, String> key = Tuple2.of(block, loc.getName());
                List<Stmt> stmts = terminatorEdges.getOrDefault(key, Tuple3.of(lastLoc, loc, new ArrayList<>())).get3();
                terminatorEdges.put(key, Tuple3.of(lastLoc, loc, stmts));
                break;
            case 3:
                XcfaLocation loc1 = locationLut.get(instruction.get3().get(1).get2());
                XcfaLocation loc2 = locationLut.get(instruction.get3().get(2).get2());

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
        XcfaEdge edge = new XcfaEdge(lastLoc, finalLoc, stmts);
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
