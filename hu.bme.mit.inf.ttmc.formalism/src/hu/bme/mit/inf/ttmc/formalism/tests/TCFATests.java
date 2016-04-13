package hu.bme.mit.inf.ttmc.formalism.tests;

import static hu.bme.mit.inf.ttmc.core.decl.impl.Decls.Const;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Leq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Neq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Rat;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Ref;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Int;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Rat;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Var;
import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.Ref;
import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.Assign;
import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.Assume;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;
import hu.bme.mit.inf.ttmc.formalism.tcfa.impl.MutableTCFA;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.TCFAPrinter;

public class TCFATests {

	@Test
	public void testCreation() {
		final VarDecl<IntType> lockd = Var("lock", Int());
		final ConstDecl<IntType> ad = Const("a", Int());
		final ConstDecl<IntType> bd = Const("b", Int());

		final TCFA fischer1 = fischer(1, lockd, ad, bd);

		System.out.println(TCFAPrinter.toGraphvizSting(fischer1));
	}

	private static TCFA fischer(final int id, final VarDecl<IntType> lockd, final ConstDecl<IntType> ad,
			final ConstDecl<IntType> bd) {

		final VarDecl<RatType> xd = Var("x_" + id, Rat());

		final VarRefExpr<RatType> x = Ref(xd);
		final VarRefExpr<IntType> lock = Ref(lockd);
		final ConstRefExpr<IntType> a = Ref(ad);
		final ConstRefExpr<IntType> b = Ref(bd);
		final RatLitExpr rzero = Rat(0, 1);
		final IntLitExpr izero = Int(0);
		final IntLitExpr i = Int(id);

		final MutableTCFA tcfa = new MutableTCFA();

		final TCFALoc l0 = tcfa.getInitLoc();
		final TCFALoc l1 = tcfa.createLoc();
		final TCFALoc l2 = tcfa.createLoc();
		final TCFALoc l3 = tcfa.createLoc();

		l1.getInvars().add(Leq(x, a));

		final TCFAEdge edge1 = tcfa.createEdge(l0, l1);
		edge1.getStmts().add(Assume(Eq(lock, izero)));
		edge1.getStmts().add(Assign(xd, rzero));

		final TCFAEdge edge2 = tcfa.createEdge(l1, l2);
		edge2.getStmts().add(Assign(xd, rzero));
		edge2.getStmts().add(Assign(lockd, i));

		final TCFAEdge edge3 = tcfa.createEdge(l2, l3);
		edge3.getStmts().add(Assume(Geq(x, b)));
		edge3.getStmts().add(Assume(Eq(lock, i)));

		final TCFAEdge edge4 = tcfa.createEdge(l2, l0);
		edge4.getStmts().add(Assume(Geq(x, b)));
		edge4.getStmts().add(Assume(Neq(lock, i)));

		final TCFAEdge edge5 = tcfa.createEdge(l3, l0);
		edge5.getStmts().add(Assign(xd, rzero));
		edge5.getStmts().add(Assign(lockd, izero));

		return tcfa;
	}

}
