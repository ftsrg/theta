package hu.bme.mit.inf.ttmc.formalism.tcfa.instances;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Leq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Neq;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Int;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Clock;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Var;
import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.Assign;
import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.Assume;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;
import hu.bme.mit.inf.ttmc.formalism.tcfa.impl.MutableTCFA;

public class ProsigmaTCFA {

	private static final Expr<IntType> NONE = Int(0);
	private static final Expr<IntType> OBJ1 = Int(1);
	private static final Expr<IntType> OBJ2 = Int(2);
	private static final Expr<IntType> OBJUP = Int(3);
	private static final Expr<IntType> OBJDOWN = Int(4);
	private static final Expr<IntType> SYNC = Int(5);

	private final Expr<IntType> tSync;
	private final Expr<IntType> tRTMax;

	private final Collection<ClockDecl> clocks;
	private final VarDecl<IntType> vchan;

	private final TCFA eth;
	private final TCFA faultModel;
	private final TCFA fieldLG;
	private final TCFA controlLG;

	public ProsigmaTCFA(final int sync, final int rtmax) {
		tSync = Int(sync);
		tRTMax = Int(rtmax);

		vchan = Var("chan", Int());

		clocks = new HashSet<>();

		eth = createETH();
		faultModel = createFaultModel();
		fieldLG = createFieldLG();
		controlLG = createControlLG();
	}

	public VarDecl<IntType> getChan() {
		return vchan;
	}

	public Collection<ClockDecl> getClocks() {
		return Collections.unmodifiableCollection(clocks);
	}

	public TCFA getETH() {
		return eth;
	}

	public TCFA getFaultModel() {
		return faultModel;
	}

	public TCFA getFieldLG() {
		return fieldLG;
	}

	public TCFA getControlLG() {
		return controlLG;
	}

	private TCFA createETH() {
		final ClockDecl vclkSync = Clock("sync");
		clocks.add(vclkSync);

		final Expr<IntType> chan = vchan.getRef();
		final Expr<RatType> clkSync = vclkSync.getRef();

		final MutableTCFA tcfa = new MutableTCFA();

		final TCFALoc init = tcfa.getInitLoc();
		init.getInvars().add(Leq(clkSync, tSync));

		{
			final TCFAEdge e1 = tcfa.createEdge(init, init);
			e1.getStmts().add(Assume(Geq(clkSync, tSync)));
			e1.getStmts().add(Assume(Eq(chan, NONE)));
			e1.getStmts().add(Assign(vchan, SYNC));
		}

		return tcfa;
	}

	private TCFA createFaultModel() {
		final Expr<IntType> chan = vchan.getRef();

		final MutableTCFA tcfa = new MutableTCFA();

		final TCFALoc init = tcfa.getInitLoc();
		final TCFALoc none = tcfa.createLoc("none");

		{
			final TCFAEdge e1 = tcfa.createEdge(init, none);
			e1.getStmts().add(Assume(Neq(chan, NONE)));
			e1.getStmts().add(Assign(vchan, NONE));
		}

		return tcfa;
	}

	private TCFA createFieldLG() {
		final ClockDecl vclkReset = Clock("fieldReset");
		clocks.add(vclkReset);

		final Expr<IntType> chan = vchan.getRef();
		final Expr<RatType> clkReset = vclkReset.getRef();

		final MutableTCFA tcfa = new MutableTCFA();

		final TCFALoc init = tcfa.getInitLoc();
		final TCFALoc tr = tcfa.createLoc("try");
		final TCFALoc conn = tcfa.createLoc("conn");

		tr.getInvars().add(Leq(clkReset, tRTMax));
		conn.getInvars().add(Leq(clkReset, tRTMax));

		{
			final TCFAEdge e1 = tcfa.createEdge(init, init);
			e1.getStmts().add(Assume(Eq(chan, OBJ2)));
			e1.getStmts().add(Assign(vchan, NONE));
		}
		{
			final TCFAEdge e2 = tcfa.createEdge(init, init);
			e2.getStmts().add(Assume(Eq(chan, OBJDOWN)));
			e2.getStmts().add(Assign(vchan, NONE));
		}
		{
			final TCFAEdge e3 = tcfa.createEdge(init, tr);
			e3.getStmts().add(Assume(Eq(chan, SYNC)));
			e3.getStmts().add(Assign(vchan, OBJ1));
			e3.getStmts().add(Assign(vclkReset, Int(0)));

		}
		{
			final TCFAEdge e4 = tcfa.createEdge(tr, tr);
			e4.getStmts().add(Assume(Eq(chan, SYNC)));
			e4.getStmts().add(Assign(vchan, OBJ1));
		}

		{
			final TCFAEdge e5 = tcfa.createEdge(tr, tr);
			e5.getStmts().add(Assume(Eq(chan, OBJDOWN)));
			e5.getStmts().add(Assign(vchan, NONE));
		}
		{
			final TCFAEdge e6 = tcfa.createEdge(tr, init);
			e6.getStmts().add(Assume(Geq(clkReset, tRTMax)));
		}
		{
			final TCFAEdge e7 = tcfa.createEdge(tr, conn);
			e7.getStmts().add(Assume(Eq(chan, OBJ2)));
			e7.getStmts().add(Assign(vclkReset, Int(0)));
		}

		{
			final TCFAEdge e8 = tcfa.createEdge(conn, init);
			e8.getStmts().add(Assume(Geq(clkReset, tRTMax)));
		}
		{
			final TCFAEdge e9 = tcfa.createEdge(conn, conn);
			e9.getStmts().add(Assume(Eq(chan, SYNC)));
			e9.getStmts().add(Assign(vchan, OBJUP));
		}
		{
			final TCFAEdge e10 = tcfa.createEdge(conn, conn);
			e10.getStmts().add(Assume(Eq(chan, OBJ2)));
			e10.getStmts().add(Assign(vchan, NONE));
		}
		{
			final TCFAEdge e11 = tcfa.createEdge(conn, conn);
			e11.getStmts().add(Assume(Eq(chan, OBJDOWN)));
			e11.getStmts().add(Assign(vchan, NONE));
			e11.getStmts().add(Assign(vclkReset, Int(0)));
		}

		return tcfa;
	}

	private TCFA createControlLG() {
		final ClockDecl vclkReset = Clock("controlReset");
		clocks.add(vclkReset);

		final Expr<IntType> chan = vchan.getRef();
		final Expr<RatType> clkReset = vclkReset.getRef();

		final MutableTCFA tcfa = new MutableTCFA();

		final TCFALoc init = tcfa.getInitLoc();
		final TCFALoc tr = tcfa.createLoc("try");
		final TCFALoc conn = tcfa.createLoc("conn");

		tr.getInvars().add(Leq(clkReset, tRTMax));
		conn.getInvars().add(Leq(clkReset, tRTMax));

		{
			final TCFAEdge e1 = tcfa.createEdge(init, init);
			e1.getStmts().add(Assume(Eq(chan, OBJUP)));
			e1.getStmts().add(Assign(vchan, NONE));
		}
		{
			final TCFAEdge e3 = tcfa.createEdge(init, tr);
			e3.getStmts().add(Assume(Eq(chan, OBJ1)));
			e3.getStmts().add(Assign(vchan, OBJ2));
			e3.getStmts().add(Assign(vclkReset, Int(0)));

		}
		{
			final TCFAEdge e5 = tcfa.createEdge(tr, tr);
			e5.getStmts().add(Assume(Eq(chan, OBJ1)));
			e5.getStmts().add(Assign(vchan, NONE));
		}
		{
			final TCFAEdge e6 = tcfa.createEdge(tr, init);
			e6.getStmts().add(Assume(Geq(clkReset, tRTMax)));
		}
		{
			final TCFAEdge e7 = tcfa.createEdge(tr, conn);
			e7.getStmts().add(Assume(Eq(chan, OBJUP)));
			e7.getStmts().add(Assign(vchan, OBJDOWN));
			e7.getStmts().add(Assign(vclkReset, Int(0)));
		}

		{
			final TCFAEdge e8 = tcfa.createEdge(conn, init);
			e8.getStmts().add(Assume(Geq(clkReset, tRTMax)));
		}
		{
			final TCFAEdge e10 = tcfa.createEdge(conn, conn);
			e10.getStmts().add(Assume(Eq(chan, OBJ1)));
			e10.getStmts().add(Assign(vchan, NONE));
		}
		{
			final TCFAEdge e11 = tcfa.createEdge(conn, conn);
			e11.getStmts().add(Assume(Eq(chan, OBJUP)));
			e11.getStmts().add(Assign(vchan, OBJDOWN));
			e11.getStmts().add(Assign(vclkReset, Int(0)));
		}

		return tcfa;
	}

}
