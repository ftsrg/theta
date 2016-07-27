package hu.bme.mit.inf.ttmc.frontend;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlockBuilder;
import hu.bme.mit.inf.ttmc.frontend.ir.ExitBlock;
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

		BasicBlock exit = new ExitBlock();

		BasicBlockBuilder thenBuilder = new BasicBlockBuilder("then");
		thenBuilder.addNode(Assign(u, Int(0)));
		thenBuilder.terminate(Goto(exit));

		BasicBlock then = thenBuilder.createBlock();

		BasicBlockBuilder bb = new BasicBlockBuilder("entry");
		bb.addNode(Assign(x, Int(3)));
		bb.addNode(Assign(y, Int(4)));
		bb.addNode(Assign(z, Add(x.getRef(), y.getRef())));
		bb.terminate(JumpIf(Not(Gt(z.getRef(), Int(3))), exit, then));

		BasicBlock entry = bb.createBlock();

		Function func = new Function("main", entry, Int());
		System.out.println(IrPrinter.toText(func));
		System.out.println(IrPrinter.toGraphvizString(func));

/*
		BasicBlock trueBranch = new BasicBlock("branch_true");
		trueBranch.addNode(Assign(z, Int(0)));

		BasicBlock entry = new BasicBlock("entry");
		entry.addNode(Assign(x, Int(3)));
		entry.addNode(Assign(y, Int(4)));
		entry.addNode(Assign(z, Add(x.getRef(), y.getRef())));
		entry.terminate(JumpIf(Eq(x.getRef(), y.getRef()), trueBranch));

		//entry.addNode(JumpIf(Eq(x.getRef(), y.getRef()), trueBranch));

		Function proc = new Function("main", entry, Int());
		proc.addLocalVariable(x);
		proc.addLocalVariable(y);
		*/
	}

}
