package hu.bme.mit.theta.xcfa.transformation.c;

import hu.bme.mit.theta.xcfa.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.xcfa.dsl.gen.CParser;
import hu.bme.mit.theta.xcfa.transformation.c.declaration.CDeclaration;

import java.util.List;

public class FunctionVisitor extends CBaseVisitor<Void> {
	public static final FunctionVisitor instance = new FunctionVisitor();

	@Override
	public Void visitDeclarationSimple(CParser.DeclarationSimpleContext ctx) {
		List<CDeclaration> declarations = DeclarationVisitor.instance.getDeclarations(ctx);
		for (CDeclaration declaration : declarations) {
			System.out.println(declaration);
		}
		return null;
	}
}
