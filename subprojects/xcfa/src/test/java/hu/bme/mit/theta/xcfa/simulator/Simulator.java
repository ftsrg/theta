package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.stmt.xcfa.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
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
            for (VarDecl var: ExprUtils.getVars(expr)) {
                if (!param.getDecls().contains(var)) {
                    param.put(var, IntExprs.Int(10));
                }
            }
        }
    }

    class CallState {
        /** current location, or where-to-return (after returning from current call) */
        Procedure procedure;
        Location currentLocation;
        ProcessState parent;

        public CallState(ProcessState parent, Procedure procedure, List<VarDecl<?>> parameters) {
            this.parent = parent;
            this.procedure = procedure;
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
                Decl<?> callerParam = callerParamsIndexed.get(i);
                VarDecl<?> calleeParam = procedure.getParams().get(i);

                parent.parent.vars.inc(calleeParam);

                int calleeParamIndex = parent.parent.vars.get(calleeParam);
                Optional<? extends LitExpr<?>> callerParameterValue = parent.parent.valuation.eval(callerParam);
                // variable could have been uninitialised
                if (callerParameterValue.isPresent())
                    parent.parent.valuation.put(calleeParam.getConstDecl(calleeParamIndex), callerParameterValue.get());
            }
            for (VarDecl var: procedure.getVars()) {
                parent.parent.vars.inc(var);
            }
        }

        /** Called when the function gets returned.
         * Deletes values associated with the current values.
         * TODO write result to the caller's variable
         */
        public void end() {
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
            push(process.getMainProcedure(), new ArrayList<>());
        }

        public void pop() {
            callStack.pop();
        }

        public boolean step() {
            if (callStack.empty())
                return false;
            return callStack.peek().step();
        }

        public void push(Procedure procedure, List<VarDecl<?>> params) {
            callStack.push(new CallState(this, procedure, params));
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
        ProcessState process = param.parent;
        process.push(stmt.getProcedure(), stmt.getParams());
        throw new UnsupportedOperationException("Not yet supported");
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
        new FillValuation().fill(unfolded, state.valuation);
        BoolLitExpr a = (BoolLitExpr) unfolded.eval(state.valuation);
        return a.getValue();
    }

    @Override
    public <DeclType extends Type> Boolean visit(AssignStmt<DeclType> stmt, CallState param) {
        Expr<? extends Type> unfolded = PathUtils.unfold(stmt.getExpr(), state.vars);

        IndexedConstDecl<DeclType> y = stmt.getVarDecl().getConstDecl(state.vars.get(stmt.getVarDecl()));
        new FillValuation().fill(unfolded, state.valuation);
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
