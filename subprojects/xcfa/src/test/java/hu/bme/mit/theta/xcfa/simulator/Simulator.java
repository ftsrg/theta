package hu.bme.mit.theta.xcfa.simulator;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.stmt.xcfa.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.XCFA.Process;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure.Edge;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure.Location;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;

import java.io.IOException;
import java.util.*;

/**
 * Checks no deadlock.
 * Checks that it ends on final location
 * Assumes no livelock (it would get to an infinite loop)
 * Uninitialised variables only work for ints (and it assigns zero), sorry
 *
 * VarIndexing is used for implementing call stack: every call digs local variables' indices one level deeper
 *
 * XcfaStmtVisitor
 */
public class Simulator implements XcfaStmtVisitor<Simulator.CallState, Boolean> {

    /**
     * Three types of variables:
     * global
     * process local
     * procedure local with parameters -> can have multiple active instances (in the stack)
     * procedures shall store how many calls have they made
     */

    static class FillValuation {
        <DeclType extends Type> void fill(Expr<DeclType> expr, MutableValuation param) {
            for (Decl var: Utils.getDecls(expr)) {
                if (!param.getDecls().contains(var)) {
                    param.put(var, IntExprs.Int(0));
                }
            }
        }

        private FillValuation() {}

        static FillValuation instance;

        public static FillValuation getInstance() {
            if (instance == null) instance = new FillValuation();
            return instance;
        }
    }

    static class Utils {

        static private void collect(Expr<? extends Type> expr, Collection<Decl<?>> collectTo) {

            if (expr instanceof RefExpr) {
                final RefExpr<?> refExpr = (RefExpr<?>) expr;
                final Decl<?> decl = refExpr.getDecl();
                collectTo.add(decl);
            }
            expr.getOps().forEach(op -> collect(op, collectTo));
        }
        static Set<Decl<?>> getDecls(Expr<? extends Type> expr) {
            Set<Decl<?>> x = new HashSet<>();
            collect(expr, x);
            return x;
        }
    }

    class CallState {
        /** current location, or where-to-return (after returning from current call) */
        Procedure procedure;
        Location currentLocation;
        ProcessState parent;
        /** Where to return the result */
        VarDecl<?> resultVar;

        public CallState(ProcessState parent, Procedure procedure, List<VarDecl<?>> parameters, VarDecl<?> resultVar) {
            this.parent = parent;
            this.procedure = procedure;
            this.resultVar = resultVar;
            currentLocation = procedure.getInitLoc();
            begin(parameters);
        }

        /** Called when the procedure gets called.
         * Pushes local variable instances. */
        public void begin(List<VarDecl<?>> parameters) {
            //  map everything *first* to the indexed version, because modifying the numbering can have effect to the variables
            // for example: gcd(a,b) call to gcd(b,a%b) would change `a`'s meaning first
            List<Decl<?>> callerParamsIndexed = new ArrayList<>(parameters);
            callerParamsIndexed.replaceAll((a)->((VarDecl<?>)a).getConstDecl(parent.parent.vars.get((VarDecl<?>)a)));

            assert(callerParamsIndexed.size() == procedure.getParams().size());
            for (int i = 0; i < parameters.size(); i++) {
                Decl<?> callerParamIndexed = callerParamsIndexed.get(i);
                VarDecl<?> calleeParam = procedure.getParams().get(i);

                parent.parent.vars.inc(calleeParam);

                int calleeParamIndex = parent.parent.vars.get(calleeParam);
                Decl<?> calleeParamIndexed = calleeParam.getConstDecl(calleeParamIndex);
                Optional<? extends LitExpr<?>> callerParameterValue = parent.parent.valuation.eval(callerParamIndexed);
                // variable could have been uninitialised
                if (callerParameterValue.isPresent())
                    parent.parent.valuation.put(calleeParamIndexed, callerParameterValue.get());
            }
            for (VarDecl var: procedure.getVars()) {
                parent.parent.vars.inc(var);
            }
            if (procedure.getResult() != null)
                parent.parent.vars.inc(procedure.getResult(), 1);
        }

        /** Called when the function gets returned.
         * Deletes values associated with the current values.
         */
        public void end() {
            // evaluate result
            Optional<? extends LitExpr<?>> result = Optional.empty();
            if (procedure.getResult() != null) {
                int index0 = parent.parent.vars.get(procedure.getResult());
                result = parent.parent.valuation.eval(procedure.getResult().getConstDecl(index0));
            }

            // pop call-stack parameters and local variables
            for (VarDecl var: procedure.getParams()) {
                int index = parent.parent.vars.get(var);
                parent.parent.valuation.remove(var.getConstDecl(index));
                parent.parent.vars.inc(var, -1);
            }
            for (VarDecl var: procedure.getVars()) {
                int index = parent.parent.vars.get(var);
                parent.parent.valuation.remove(var.getConstDecl(index));
                parent.parent.vars.inc(var, -1);
            }

            // write result
            if (procedure.getResult() != null) {
                Preconditions.checkState(result.isPresent(), "Procedure has return value, but nothing is returned.");
                parent.parent.vars.inc(procedure.getResult(), -1);

                Decl<? extends Type> resultDecl = resultVar.getConstDecl(parent.parent.vars.get(resultVar));
                if (result.isPresent())
                    parent.parent.valuation.put(resultDecl, result.get());
            } else {
                Preconditions.checkState(!result.isPresent(), "Procedure has no return value, but something is returned.");
            }

            parent.pop();
        }
        // returning from a function counts as a step
        public boolean step() {
            if (currentLocation == procedure.getFinalLoc()) {
                end();
                return true;
            }
            for (Edge edge: currentLocation.getOutgoingEdges()) {
                assert(edge.getStmts().size() == 1);
                // XXX dangerous: some special stmt could mess up everything with multiple statements:
                // L0 -> L1 {
                //   call proc()
                //   a = a + 2
                // }
                // this code would try to call proc(), then increment a by 2, and *only then* proceed to the call itself.
                for (Stmt stmt: edge.getStmts()) {
                    if (stmt.accept((XcfaStmtVisitor<CallState,Boolean>)parent.parent.simulator, this)) {
                        currentLocation = edge.getTarget();
                        // test that the procedure did not get to the error location
                        assert(currentLocation != procedure.getErrorLoc());
                        // step succeeded
                        return true;
                    }
                }
            }
            return false;
        }
    }

    class ProcessState {
        Stack<CallState> callStack;
        Process process;
        RuntimeState parent;
        public ProcessState(RuntimeState parent, Process process) {
            this.parent = parent;
            callStack = new Stack<>();
            this.process = process;
            push(process.getMainProcedure(), new ArrayList<>(), null);
        }

        public void pop() {
            callStack.pop();
        }

        public boolean step() {
            if (callStack.empty())
                return false;
            return callStack.peek().step();
        }

        public void push(Procedure procedure, List<VarDecl<?>> params, VarDecl<?> resultVar) {
            callStack.push(new CallState(this, procedure, params, resultVar));
        }
    }

    class RuntimeState {
        List<ProcessState> processStates;
        XCFA xcfa;
        Simulator simulator;
        MutableValuation valuation;
        VarIndexing vars;
        public RuntimeState(Simulator simulator, XCFA xcfa) {
            valuation = new MutableValuation();
            vars = VarIndexing.builder(0).build();
            vars = VarIndexing.builder(1).build();
            this.simulator = simulator;
            this.xcfa = xcfa;
            List<Process> procs = xcfa.getProcesses();
            processStates = new ArrayList<>();
            for (Process proc: procs) {
                processStates.add(new ProcessState(this, proc));
            }
        }

        /** Steps in a deterministic way */
        public boolean step() {
            for (ProcessState state: processStates) {
                if (state.step()) {
                    return true;
                }
            }
            return false;
        }
    }

    private RuntimeState state;

    public Simulator(XCFA xcfa) throws IOException {
        state = new RuntimeState(this, xcfa);
        while (true) {
            if (!state.step()) {
                break;
            }
        }
    }

    @Override
    public Boolean visit(XcfaCallStmt _stmt, CallState param) {
        assert(_stmt instanceof CallStmt);
        CallStmt stmt = (CallStmt) _stmt;
        // paraméterek befelé: stmt.getParams()
        // az, amit hívnak: stmt.getProcedure()
        // visszatérési értéket stmt.getVar()-ba kell írni
        ProcessState process = param.parent;
        process.push(stmt.getProcedure(), stmt.getParams(), stmt.isVoid() ? null : stmt.getVar());
        return true;
    }

    @Override
    public Boolean visit(StoreStmt storeStmt, CallState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Boolean visit(LoadStmt loadStmt, CallState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Boolean visit(AtomicBeginStmt atomicBeginStmt, CallState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Boolean visit(AtomicEndStmt atomicEndStmt, CallState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Boolean visit(NotifyAllStmt notifyAllStmt, CallState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Boolean visit(NotifyStmt notifyStmt, CallState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Boolean visit(WaitStmt waitStmt, CallState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Boolean visit(SkipStmt stmt, CallState param) {
        return true;
    }

    @Override
    public Boolean visit(AssumeStmt stmt, CallState param) {
        Expr<BoolType> unfolded = PathUtils.unfold(stmt.getCond(), state.vars);
        FillValuation.getInstance().fill(unfolded, state.valuation);
        BoolLitExpr a = (BoolLitExpr) unfolded.eval(state.valuation);
        return a.getValue();
    }

    @Override
    public <DeclType extends Type> Boolean visit(AssignStmt<DeclType> stmt, CallState param) {
        Expr<? extends Type> unfolded = PathUtils.unfold(stmt.getExpr(), state.vars);

        IndexedConstDecl<DeclType> y = stmt.getVarDecl().getConstDecl(state.vars.get(stmt.getVarDecl()));
        FillValuation.getInstance().fill(unfolded, state.valuation);
        LitExpr x = unfolded.eval(state.valuation);
        state.valuation.put(y, x);
        return true;
    }

    @Override
    public <DeclType extends Type> Boolean visit(HavocStmt<DeclType> stmt, CallState param) {
        state.valuation.remove(stmt.getVarDecl());
        return true;
    }

    @Override
    public Boolean visit(XcfaStmt xcfaStmt, CallState param) {
        return xcfaStmt.accept(this, param);
    }
}
