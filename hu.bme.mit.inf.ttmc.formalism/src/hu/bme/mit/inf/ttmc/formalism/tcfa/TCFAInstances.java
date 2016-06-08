package hu.bme.mit.inf.ttmc.formalism.tcfa;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Leq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Neq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Rat;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Clock;
import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.Assign;
import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.Assume;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.tcfa.impl.MutableTCFA;

public final class TCFAInstances {

	private TCFAInstances() {
	}

	public static TCFA fischer(final int id, final int ia, final int ib, final VarDecl<IntType> vlock) {

		final ClockDecl cx = Clock("x_" + id);

		final Expr<RatType> x = cx.getRef();
		final Expr<IntType> lock = vlock.getRef();

		final Expr<IntType> i = Int(id);
		final Expr<IntType> a = Int(ia);
		final Expr<IntType> b = Int(ib);

		final Expr<RatType> rzero = Rat(0, 1);
		final Expr<IntType> izero = Int(0);

		final MutableTCFA tcfa = new MutableTCFA();

		final TCFALoc l0 = tcfa.getInitLoc();
		final TCFALoc l1 = tcfa.createLoc();
		final TCFALoc l2 = tcfa.createLoc();
		final TCFALoc l3 = tcfa.createLoc();

		l1.getInvars().add(Leq(x, a));

		final TCFAEdge edge1 = tcfa.createEdge(l0, l1);
		edge1.getStmts().add(Assume(Eq(lock, izero)));
		edge1.getStmts().add(Assign(cx, rzero));

		final TCFAEdge edge2 = tcfa.createEdge(l1, l2);
		edge2.getStmts().add(Assign(cx, rzero));
		edge2.getStmts().add(Assign(vlock, i));

		final TCFAEdge edge3 = tcfa.createEdge(l2, l3);
		edge3.getStmts().add(Assume(Geq(x, b)));
		edge3.getStmts().add(Assume(Eq(lock, i)));

		final TCFAEdge edge4 = tcfa.createEdge(l2, l0);
		edge4.getStmts().add(Assume(Geq(x, b)));
		edge4.getStmts().add(Assume(Neq(lock, i)));

		final TCFAEdge edge5 = tcfa.createEdge(l3, l0);
		edge5.getStmts().add(Assign(cx, rzero));
		edge5.getStmts().add(Assign(vlock, izero));

		return tcfa;
	}

}
