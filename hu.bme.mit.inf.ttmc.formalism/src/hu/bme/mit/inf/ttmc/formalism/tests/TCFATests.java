package hu.bme.mit.inf.ttmc.formalism.tests;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.factory.StmtFactory;
import hu.bme.mit.inf.ttmc.formalism.program.ProgramManager;
import hu.bme.mit.inf.ttmc.formalism.program.factory.ProgramDeclFactory;
import hu.bme.mit.inf.ttmc.formalism.program.factory.ProgramExprFactory;
import hu.bme.mit.inf.ttmc.formalism.program.factory.ProgramTypeFactory;
import hu.bme.mit.inf.ttmc.formalism.program.impl.ProgramManagerImpl;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;
import hu.bme.mit.inf.ttmc.formalism.tcfa.impl.MutableTCFA;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.TCFAPrinter;

public class TCFATests {

	@Test
	public void testCreation() {
		final ProgramManager manager = new ProgramManagerImpl(new ConstraintManagerImpl());

		final VarDecl<IntType> lockd = manager.getDeclFactory().Var("lock", manager.getTypeFactory().Int());
		final ConstDecl<IntType> ad = manager.getDeclFactory().Const("a", manager.getTypeFactory().Int());
		final ConstDecl<IntType> bd = manager.getDeclFactory().Const("b", manager.getTypeFactory().Int());

		final TCFA fischer1 = fischer(manager, 1, lockd, ad, bd);

		System.out.println(TCFAPrinter.toGraphvizSting(fischer1));
	}

	private static TCFA fischer(final ProgramManager manager, final int id, final VarDecl<IntType> lockd,
			final ConstDecl<IntType> ad, final ConstDecl<IntType> bd) {
		final ProgramTypeFactory tf = manager.getTypeFactory();
		final ProgramDeclFactory df = manager.getDeclFactory();
		final ProgramExprFactory ef = manager.getExprFactory();
		final StmtFactory sf = manager.getStmtFactory();

		final VarDecl<RatType> xd = df.Var("x_" + id, tf.Rat());

		final VarRefExpr<RatType> x = ef.Ref(xd);
		final VarRefExpr<IntType> lock = ef.Ref(lockd);
		final ConstRefExpr<IntType> a = ef.Ref(ad);
		final ConstRefExpr<IntType> b = ef.Ref(bd);
		final RatLitExpr rzero = ef.Rat(0, 1);
		final IntLitExpr izero = ef.Int(0);
		final IntLitExpr i = ef.Int(id);

		final MutableTCFA tcfa = new MutableTCFA();

		final TCFALoc l0 = tcfa.getInitLoc();
		final TCFALoc l1 = tcfa.createLoc();
		final TCFALoc l2 = tcfa.createLoc();
		final TCFALoc l3 = tcfa.createLoc();

		l1.getInvars().add(ef.Leq(x, a));

		final TCFAEdge edge1 = tcfa.createEdge(l0, l1);
		edge1.getStmts().add(sf.Assume(ef.Eq(lock, izero)));
		edge1.getStmts().add(sf.Assign(xd, rzero));

		final TCFAEdge edge2 = tcfa.createEdge(l1, l2);
		edge2.getStmts().add(sf.Assign(xd, rzero));
		edge2.getStmts().add(sf.Assign(lockd, i));

		final TCFAEdge edge3 = tcfa.createEdge(l2, l3);
		edge3.getStmts().add(sf.Assume(ef.Geq(x, b)));
		edge3.getStmts().add(sf.Assume(ef.Eq(lock, i)));

		final TCFAEdge edge4 = tcfa.createEdge(l2, l0);
		edge4.getStmts().add(sf.Assume(ef.Geq(x, b)));
		edge4.getStmts().add(sf.Assume(ef.Neq(lock, i)));

		final TCFAEdge edge5 = tcfa.createEdge(l3, l0);
		edge5.getStmts().add(sf.Assign(xd, rzero));
		edge5.getStmts().add(sf.Assign(lockd, izero));

		return tcfa;
	}

}
