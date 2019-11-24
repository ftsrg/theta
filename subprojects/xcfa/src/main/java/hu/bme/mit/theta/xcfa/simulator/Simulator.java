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
public class Simulator {

	private RuntimeState state;
    private final Scheduler s = enabledTransitions -> enabledTransitions.iterator().next();

	public Simulator(XCFA xcfa) {
		state = new RuntimeState(this, xcfa);
	}

	boolean step() {
	    return state.step(s);
    }

}
