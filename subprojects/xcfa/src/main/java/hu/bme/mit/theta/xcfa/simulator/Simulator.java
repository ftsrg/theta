package hu.bme.mit.theta.xcfa.simulator;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.stmt.xcfa.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;

import java.io.IOException;
import java.util.*;

/**
 * Checks no deadlock.
 * Checks that it ends on final location
 * Assumes no livelock (it would get to an infinite loop)
 * Uninitialised variables only work for ints (and it assigns zero), sorry
 * <p>
 * VarIndexing is used for implementing call stack: every call digs local variables' indices one level deeper
 * <p>
 * XcfaStmtVisitor
 */
public class Simulator implements XcfaStmtVisitor<CallState, Boolean> {

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
	    Preconditions.checkArgument(_stmt instanceof CallStmt, "XcfaCallStmt should be a CallStmt!");
		CallStmt stmt = (CallStmt) _stmt;
		// paraméterek befelé: stmt.getParams()
		// az, amit hívnak: stmt.getProcedure()
		// visszatérési értéket stmt.getVar()-ba kell írni
		ProcessState process = param.parent;
		if (stmt.isVoid()) {
            process.push(stmt.getProcedure(), stmt.getParams());
        } else {
            process.push(stmt.getProcedure(), stmt.getParams(), stmt.getVar());
        }
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
