package hu.bme.mit.theta.xcfa.transformation.c;

import hu.bme.mit.theta.xcfa.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.xcfa.dsl.gen.CParser;
import hu.bme.mit.theta.xcfa.transformation.c.declaration.CDeclaration;
import org.antlr.v4.runtime.Token;

import java.util.List;

public class TestVisitor extends CBaseVisitor<Void> {
	public static final TestVisitor instance = new TestVisitor();
	@Override
	public Void visitDeclaration(CParser.DeclarationContext ctx) {
		System.out.print("Start: ");
		printPosInfo(ctx.getStart());
		System.out.print("Stop: ");
		printPosInfo(ctx.getStop());
		List<CDeclaration> declarations = DeclarationVisitor.instance.getDeclarations(ctx);
		for (CDeclaration declaration : declarations) {
			System.out.println(declaration);
		}
		return null;
	}

	private void printPosInfo(Token symbol) {
		StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append("startIndex: ").append(symbol.getStartIndex()).append(", ");
		stringBuilder.append("stopIndex: ").append(symbol.getStopIndex()).append(", ");
		stringBuilder.append("line: ").append(symbol.getLine()).append(", ");
		stringBuilder.append("column: ").append(symbol.getCharPositionInLine());
		System.out.println(stringBuilder);
	}
}
