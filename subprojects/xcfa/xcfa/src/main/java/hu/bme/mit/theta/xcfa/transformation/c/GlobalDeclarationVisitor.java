package hu.bme.mit.theta.xcfa.transformation.c;

import hu.bme.mit.theta.xcfa.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.xcfa.dsl.gen.CParser;

import java.util.ArrayList;
import java.util.List;

public class GlobalDeclarationVisitor extends CBaseVisitor<List<String>> {

	@Override
	public List<String> visitFunctionDefinition(CParser.FunctionDefinitionContext ctx) {
		return null;
	}

	@Override
	public List<String> visitGlobalDeclaration(CParser.GlobalDeclarationContext ctx) {
		return ctx.declaration().accept(this);
	}

	@Override
	public List<String> visitDeclarationStatic(CParser.DeclarationStaticContext ctx) {
		throw new UnsupportedOperationException("Not yet implemented!");
	}

	@Override
	public List<String> visitDeclarationSimple(CParser.DeclarationSimpleContext ctx) {
		List<String> declarationSpecifiers = ctx.declarationSpecifiers().accept(this);
		List<String> declarationIdentifiers = ctx.initDeclaratorList().accept(this);
		System.out.println(declarationSpecifiers + " " + declarationIdentifiers);
		return null;
	}

	@Override
	public List<String> visitDeclarationSpecifiers(CParser.DeclarationSpecifiersContext ctx) {
		List<String> ret = new ArrayList<>();
		for (CParser.DeclarationSpecifierContext declarationSpecifierContext : ctx.declarationSpecifier()) {
			ret.add(declarationSpecifierContext.getText());
		}
		return ret;
	}

	@Override
	public List<String> visitInitDeclaratorList(CParser.InitDeclaratorListContext ctx) {
		List<String> ret = new ArrayList<>();
		for (CParser.InitDeclaratorContext context : ctx.initDeclarator()) {
			ret.add(context.getText());
		}
		return ret;
	}
}
