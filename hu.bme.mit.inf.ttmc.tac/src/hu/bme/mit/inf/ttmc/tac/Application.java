package hu.bme.mit.inf.ttmc.tac;

import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.tac.ir.GlobalContext;
import hu.bme.mit.inf.ttmc.tac.ir.Procedure;
import static hu.bme.mit.inf.ttmc.core.decl.impl.Decls.*;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.*;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.*;

import java.util.ArrayList;
import java.util.List;

public class Application {

	public static void main(String[] args) {
		List<ParamDecl<? extends Type>> params = new ArrayList<>();
		params.add(Param("left", Int()));
		ProcDecl<IntType> calcProc = Proc("calculate", params, Int());

		Procedure main = new Procedure(calcProc);

		GlobalContext context = new GlobalContext();
		context.addProcedure(main);
	}

}
