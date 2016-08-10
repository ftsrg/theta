package hu.bme.mit.inf.ttmc.formalism.tcfa.instances;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Leq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Neq;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Clock;
import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.Assign;
import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.Assume;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;
import hu.bme.mit.inf.ttmc.formalism.tcfa.impl.MutableTCFA;

public final class FischerTCFA {

	private final MutableTCFA tcfa;

	private final int id;
	private final VarDecl<IntType> vlock;
	private final ClockDecl cx;

	private final TCFALoc initial;
	private final TCFALoc critical;

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

	public TCFALoc getInitial() {
		return initial;
	}

	public TCFALoc getCritical() {
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

		tcfa = new MutableTCFA();
		cx = Clock("x_" + id);

		final Expr<RatType> x = cx.getRef();
		final Expr<IntType> lock = vlock.getRef();

		final Expr<IntType> i = Int(id);
		final Expr<IntType> a = Int(ia);
		final Expr<IntType> b = Int(ib);

		final Expr<IntType> zero = Int(0);

		final TCFALoc l0 = tcfa.createLoc("sleep", false, ImmutableSet.of());
		final TCFALoc l1 = tcfa.createLoc("wait", false, ImmutableSet.of(Leq(x, a)));
		final TCFALoc l2 = tcfa.createLoc("try", false, ImmutableSet.of());
		final TCFALoc l3 = tcfa.createLoc("crit", false, ImmutableSet.of());
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
