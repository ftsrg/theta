package hu.bme.mit.inf.ttmc.formalism.tests;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.factory.VarDeclFactory;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.factory.STSExprFactory;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSManagerImpl;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;

public class FormalismExprITEEliminatorTests {
	// Manager and factories
	STSManager manager;
	private VarDeclFactory dfc;
	private TypeFactory tfc;
	private STSExprFactory efc;
	// Constants and variables for testing
	private VarRefExpr<BoolType> vA, vB, vC;

	@Before
	public void before() {
		// Create manager and get factories
		manager = new STSManagerImpl(new ConstraintManagerImpl());
		dfc = manager.getDeclFactory();
		efc = manager.getExprFactory();
		tfc = manager.getTypeFactory();
		// Create constants and variables
		vA = dfc.Var("A", tfc.Bool()).getRef();
		vB = dfc.Var("B", tfc.Bool()).getRef();
		vC = dfc.Var("C", tfc.Bool()).getRef();
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testProgExprIteEliminator() {
		// if A then B else C
		Assert.assertEquals(FormalismUtils.eliminate(efc.Ite(vA, vB, vC), manager),
				efc.And(efc.Or(efc.Not(vA), vB), efc.Or(vA, vC)));
		// (if A then B else C)'
		Assert.assertEquals(FormalismUtils.eliminate(efc.Prime(efc.Ite(vA, vB, vC)), manager),
				efc.And(efc.Or(efc.Not(vA), efc.Prime(vB)), efc.Or(vA, efc.Prime(vC))));
	}
}
