package hu.bme.mit.inf.theta.frontend;

public class Application {

	public static void main(String[] args) {
		/*
		VarDecl<IntType> x = Var("x", Int());
		VarDecl<IntType> y = Var("y", Int());
		VarDecl<IntType> z = Var("z", Int());
		VarDecl<IntType> u = Var("u", Int());

		Function func = new Function("main", Int());
		Function func2 = new Function("main2", Int());

		BasicBlock then = new BasicBlock("if0_then", func2);
		then.addNode(Assign(u, Int(0)));
		then.terminate(Goto(func.getExitBlock()));

		BasicBlock entry = new BasicBlock("entry", func);
		entry.addNode(Assign(x, Int(3)));
		entry.addNode(Assign(y, Int(4)));
		entry.addNode(Assign(z, Add(x.getRef(), y.getRef())));
		entry.terminate(JumpIf(Gt(z.getRef(), Int(3)), then, func.getExitBlock()));

		func.setEntryBlock(entry);
		func2.setEntryBlock(then);

		//System.out.println(IrPrinter.toText(func));
		System.out.println(IrPrinter.toGraphvizString(func));
		System.out.println(IrPrinter.toGraphvizString(func2)); */



	}

}
