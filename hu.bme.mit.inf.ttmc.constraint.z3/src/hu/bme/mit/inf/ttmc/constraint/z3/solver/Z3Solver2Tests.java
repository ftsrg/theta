package hu.bme.mit.inf.ttmc.constraint.z3.solver;

import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.SolverFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.solver.Model;
import hu.bme.mit.inf.ttmc.constraint.solver.Solver;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.z3.Z3ConstraintManager;

public class Z3Solver2Tests {

	TypeFactory tf;
	DeclFactory df;
	ExprFactory ef;

	Solver solver;

	ConstDecl<IntType> ad;
	ConstDecl<IntType> bd;
	ConstDecl<IntType> cd;
	ConstDecl<IntType> dd;

	Expr<IntType> a;
	Expr<IntType> b;
	Expr<IntType> c;
	Expr<IntType> d;

	@Before
	public void initialize() {
		final ConstraintManager manager = new Z3ConstraintManager();
		final SolverFactory sf = manager.getSolverFactory();

		tf = manager.getTypeFactory();
		df = manager.getDeclFactory();
		ef = manager.getExprFactory();
		solver = sf.createSolver(true, true);

		ad = df.Const("a", tf.Int());
		bd = df.Const("b", tf.Int());
		cd = df.Const("c", tf.Int());
		dd = df.Const("d", tf.Int());

		a = ef.Ref(ad);
		b = ef.Ref(bd);
		c = ef.Ref(cd);
		d = ef.Ref(dd);
	}

	@Test
	public void testSimple() {
		solver.add(ef.Gt(a, b));

		solver.check();
		final Model model = solver.getModel();

		System.out.println(model.eval(ad));
		System.out.println(model.eval(bd));
	}

}
