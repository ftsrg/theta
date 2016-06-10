package hu.bme.mit.inf.ttmc.formalism.tests;

import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Int;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Var;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.formalism.tcfa.instances.FischerTCFA;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.TCFAPrinter;

public class TCFATests {

	@Test
	public void testCreation() {
		final VarDecl<IntType> vlock = Var("lock", Int());
		final TCFA fischer1 = new FischerTCFA(1, 1, 2, vlock).getTCFA();
		System.out.println(TCFAPrinter.toGraphvizSting(fischer1));
	}

}
