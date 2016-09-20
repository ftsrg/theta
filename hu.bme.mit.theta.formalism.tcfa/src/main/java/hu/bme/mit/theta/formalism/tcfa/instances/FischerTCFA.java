package hu.bme.mit.theta.formalism.tcfa.instances;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Leq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Neq;
import static hu.bme.mit.theta.core.stmt.impl.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.impl.Stmts.Assume;
import static hu.bme.mit.theta.formalism.common.decl.impl.Decls2.Clock;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.formalism.tcfa.impl.SimpleTcfa;

@Deprecated
public final class FischerTCFA {

	private final SimpleTcfa tcfa;

	private final int id;
	private final VarDecl<IntType> vlock;
	private final ClockDecl cx;

	private final TcfaLoc initial;
	private final TcfaLoc critical;

	////

	public TCFA getTCFA() {
		return tcfa;
	}

	public int getId() {
		return id;
	}

	public VarDecl<IntType> getLock() {
		return vlock;
	}

	public ClockDecl getClock() {
		return cx;
	}

	public TcfaLoc getInitial() {
		return initial;
	}

	public TcfaLoc getCritical() {
		return critical;
	}

	////

	public FischerTCFA(final int id, final int ia, final int ib, final VarDecl<IntType> vlock) {
		checkArgument(id > 0);
		checkArgument(ia >= 0);
		checkArgument(ib >= 0);
		checkNotNull(vlock);

		this.id = id;
		this.vlock = vlock;

		tcfa = new SimpleTcfa();
		cx = Clock("x_" + id);

		final Expr<RatType> x = cx.getRef();
		final Expr<IntType> lock = vlock.getRef();

		final Expr<IntType> i = Int(id);
		final Expr<IntType> a = Int(ia);
		final Expr<IntType> b = Int(ib);

		final Expr<IntType> zero = Int(0);

		final TcfaLoc l0 = tcfa.createLoc("sleep", false, ImmutableSet.of());
		final TcfaLoc l1 = tcfa.createLoc("wait", false, ImmutableSet.of(Leq(x, a)));
		final TcfaLoc l2 = tcfa.createLoc("try", false, ImmutableSet.of());
		final TcfaLoc l3 = tcfa.createLoc("crit", false, ImmutableSet.of());
		tcfa.setInitLoc(l0);

		initial = l0;
		critical = l3;

		tcfa.createEdge(l0, l1, ImmutableList.of(Assume(Eq(lock, zero)), Assign(cx, zero)));
		tcfa.createEdge(l1, l2, ImmutableList.of(Assign(cx, zero), Assign(vlock, i)));
		tcfa.createEdge(l2, l3, ImmutableList.of(Assume(Geq(x, b)), Assume(Eq(lock, i))));
		tcfa.createEdge(l2, l0, ImmutableList.of(Assume(Geq(x, b)), Assume(Neq(lock, i))));
		tcfa.createEdge(l3, l0, ImmutableList.of(Assign(vlock, zero)));
	}

}
