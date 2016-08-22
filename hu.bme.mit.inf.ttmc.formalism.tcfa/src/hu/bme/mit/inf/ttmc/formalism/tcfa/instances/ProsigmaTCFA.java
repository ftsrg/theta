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

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;
import hu.bme.mit.inf.ttmc.formalism.tcfa.impl.SimpleTCFA;

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

		final SimpleTCFA tcfa = new SimpleTCFA();

		final TCFALoc init = tcfa.createLoc("init", false, ImmutableSet.of(Leq(clkSync, tSync)));
		tcfa.setInitLoc(init);
		tcfa.createEdge(init, init,
				ImmutableList.of(Assume(Geq(clkSync, tSync)), Assume(Eq(chan, NONE)), Assign(vchan, SYNC)));

		return tcfa;
	}

	private TCFA createFaultModel() {
		final Expr<IntType> chan = vchan.getRef();

		final SimpleTCFA tcfa = new SimpleTCFA();

		final TCFALoc init = tcfa.createLoc("init", false, ImmutableSet.of());
		final TCFALoc none = tcfa.createLoc("none", false, ImmutableSet.of());

		tcfa.setInitLoc(init);

		tcfa.createEdge(init, none, ImmutableList.of(Assume(Neq(chan, NONE)), Assign(vchan, NONE)));

		return tcfa;
	}

	private TCFA createFieldLG() {
		final ClockDecl vclkReset = Clock("fieldReset");
		clocks.add(vclkReset);

		final Expr<IntType> chan = vchan.getRef();
		final Expr<RatType> clkReset = vclkReset.getRef();

		final SimpleTCFA tcfa = new SimpleTCFA();

		final TCFALoc init = tcfa.createLoc("init", false, ImmutableSet.of());
		final TCFALoc tr = tcfa.createLoc("try", false, ImmutableSet.of(Leq(clkReset, tRTMax)));
		final TCFALoc conn = tcfa.createLoc("conn", false, ImmutableSet.of(Leq(clkReset, tRTMax)));

		tcfa.setInitLoc(init);

		tcfa.createEdge(init, init, ImmutableList.of(Assume(Eq(chan, OBJ2)), Assign(vchan, NONE)));
		tcfa.createEdge(init, init, ImmutableList.of(Assume(Eq(chan, OBJDOWN)), Assign(vchan, NONE)));
		tcfa.createEdge(init, tr,
				ImmutableList.of(Assume(Eq(chan, SYNC)), Assign(vchan, OBJ1), Assign(vclkReset, Int(0))));
		tcfa.createEdge(tr, tr, ImmutableList.of(Assume(Eq(chan, SYNC)), Assign(vchan, OBJ1)));
		tcfa.createEdge(tr, tr, ImmutableList.of(Assume(Eq(chan, OBJDOWN)), Assign(vchan, NONE)));
		tcfa.createEdge(tr, init, ImmutableList.of(Assume(Geq(clkReset, tRTMax))));
		tcfa.createEdge(tr, conn, ImmutableList.of(Assume(Eq(chan, OBJ2)), Assign(vclkReset, Int(0))));
		tcfa.createEdge(conn, init, ImmutableList.of(Assume(Geq(clkReset, tRTMax))));
		tcfa.createEdge(conn, conn, ImmutableList.of(Assume(Eq(chan, SYNC)), Assign(vchan, OBJUP)));
		tcfa.createEdge(conn, conn, ImmutableList.of(Assume(Eq(chan, OBJ2)), Assign(vchan, NONE)));
		tcfa.createEdge(conn, conn,
				ImmutableList.of(Assume(Eq(chan, OBJDOWN)), Assign(vchan, NONE), Assign(vclkReset, Int(0))));

		return tcfa;
	}

	private TCFA createControlLG() {
		final ClockDecl vclkReset = Clock("controlReset");
		clocks.add(vclkReset);

		final Expr<IntType> chan = vchan.getRef();
		final Expr<RatType> clkReset = vclkReset.getRef();

		final SimpleTCFA tcfa = new SimpleTCFA();

		final TCFALoc init = tcfa.createLoc("init", false, ImmutableSet.of());
		final TCFALoc tr = tcfa.createLoc("try", false, ImmutableSet.of(Leq(clkReset, tRTMax)));
		final TCFALoc conn = tcfa.createLoc("conn", false, ImmutableSet.of(Leq(clkReset, tRTMax)));

		tcfa.setInitLoc(init);

		tcfa.createEdge(init, init, ImmutableList.of(Assume(Eq(chan, OBJUP)), Assign(vchan, NONE)));
		tcfa.createEdge(init, tr,
				ImmutableList.of(Assume(Eq(chan, OBJ1)), Assign(vchan, OBJ2), Assign(vclkReset, Int(0))));
		tcfa.createEdge(tr, tr, ImmutableList.of(Assume(Eq(chan, OBJ1)), Assign(vchan, NONE)));
		tcfa.createEdge(tr, init, ImmutableList.of(Assume(Geq(clkReset, tRTMax))));
		tcfa.createEdge(tr, conn,
				ImmutableList.of(Assume(Eq(chan, OBJUP)), Assign(vchan, OBJDOWN), Assign(vclkReset, Int(0))));
		tcfa.createEdge(conn, init, ImmutableList.of(Assume(Geq(clkReset, tRTMax))));
		tcfa.createEdge(conn, conn, ImmutableList.of(Assume(Eq(chan, OBJ1)), Assign(vchan, NONE)));
		tcfa.createEdge(conn, conn,
				ImmutableList.of(Assume(Eq(chan, OBJUP)), Assign(vchan, OBJDOWN), Assign(vclkReset, Int(0))));

		return tcfa;
	}

}
