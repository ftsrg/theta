package hu.bme.mit.inf.ttmc.formalism.tests;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.sts.STSFactory;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSFactoryImpl;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismExprITEEliminator;

public class FormalismExprITEEliminatorTests {
	// Manager and factories
	private ConstraintManager manager;
	private ExprFactory efc;
	private TypeFactory tfc;
	private STSFactory sfc;
	// Constants and variables for testing
	private VarRefExpr<BoolType> vA, vB, vC;
	// Transformator
	FormalismExprITEEliminator eliminator;
	
	@Before
	public void before() {
		// Create manager and get factories
		manager = new ConstraintManagerImpl();
		efc = manager.getExprFactory();
		tfc = manager.getTypeFactory();
		sfc = new STSFactoryImpl();
		// Create constants and variables
		vA = sfc.Var("A", tfc.Bool()).getRef();
		vB = sfc.Var("B", tfc.Bool()).getRef();
		vC = sfc.Var("C", tfc.Bool()).getRef();
		// Create transformator
		eliminator = new FormalismExprITEEliminator(manager);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testProgExprIteEliminator() {
		// if A then B else C
		Assert.assertEquals(
				eliminator.eliminate(efc.Ite(vA, vB, vC)),
				efc.And(efc.Or(efc.Not(vA), vB), efc.Or(vA, vC))
				);
		// (if A then B else C)'
		Assert.assertEquals(
				eliminator.eliminate(sfc.Prime(efc.Ite(vA, vB, vC))),
				efc.And(efc.Or(efc.Not(vA), sfc.Prime(vB)), efc.Or(vA, sfc.Prime(vC)))
				);
	}
}
