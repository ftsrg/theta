package hu.bme.mit.inf.ttmc.frontend;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.node.IrNode;
import hu.bme.mit.inf.ttmc.frontend.ir.utils.IrPrinter;

import static hu.bme.mit.inf.ttmc.core.type.impl.Types.*;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.*;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.*;

import static hu.bme.mit.inf.ttmc.frontend.ir.node.NodeFactory.*;

import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;


public class Application {

	public static void main(String[] args) {
		VarDecl<IntType> x = Var("x", Int());
		VarDecl<IntType> y = Var("y", Int());
		VarDecl<IntType> z = Var("z", Int());
		VarDecl<IntType> u = Var("u", Int());

		Function func = new Function("main", Int());

		BasicBlock then = new BasicBlock("if0_then", func);
		then.addNode(Assign(u, Int(0)));
		then.terminate(Goto(func.getExitBlock()));

		BasicBlock entry = new BasicBlock("entry", func);
		entry.addNode(Assign(x, Int(3)));
		entry.addNode(Assign(y, Int(4)));
		entry.addNode(Assign(z, Add(x.getRef(), y.getRef())));
		entry.terminate(JumpIf(Gt(z.getRef(), Int(3)), then, func.getExitBlock()));

		func.setEntryBlock(entry);

		//System.out.println(IrPrinter.toText(func));
		System.out.println(IrPrinter.toGraphvizString(func));
	}

}
