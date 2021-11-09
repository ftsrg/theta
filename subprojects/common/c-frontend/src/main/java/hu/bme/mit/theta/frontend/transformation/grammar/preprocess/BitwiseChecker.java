package hu.bme.mit.theta.frontend.transformation.grammar.preprocess;

import hu.bme.mit.theta.c.frontend.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;

import java.util.List;

import static com.google.common.base.Preconditions.checkState;

public class BitwiseChecker extends CBaseVisitor<Void> {
	public static final BitwiseChecker instance = new BitwiseChecker();
	private static BitwiseOption bitwiseOption = null;

	// checks only once, returns the result of the first check after
	public BitwiseOption checkIfBitwise(List<CParser.ExternalDeclarationContext> contexts) {
		bitwiseOption = BitwiseOption.INTEGER;
		for (CParser.ExternalDeclarationContext ctx : contexts) {
			ctx.accept(instance);
		}
		checkState(bitwiseOption!=null);
		return bitwiseOption;
	}

	// will return null, if not checked with checkIfBitwise() first!
	public static BitwiseOption getBitwiseOption() { return bitwiseOption; }

	@Override
	public Void visitTypeSpecifierDouble(CParser.TypeSpecifierDoubleContext ctx) {
		bitwiseOption = BitwiseOption.BITWISE_FLOAT;
		return null;
	}

	@Override
	public Void visitTypeSpecifierFloat(CParser.TypeSpecifierFloatContext ctx) {
		bitwiseOption = BitwiseOption.BITWISE_FLOAT;
		return null;
	}

	@Override
	public Void visitPrimaryExpressionConstant(CParser.PrimaryExpressionConstantContext ctx) {
		String text = ctx.getText();
		if(text.contains(".")) {
			bitwiseOption = BitwiseOption.BITWISE_FLOAT;
			return null;
		}
		return super.visitPrimaryExpressionConstant(ctx);
	}

	@Override
	public Void visitInclusiveOrExpression(CParser.InclusiveOrExpressionContext ctx) {
		ctx.exclusiveOrExpression(0).accept(this);
		Boolean b = ctx.exclusiveOrExpression().size() > 1;
		if(b) {
			if(bitwiseOption==BitwiseOption.INTEGER) bitwiseOption = BitwiseOption.BITWISE;
		}
		return null;
	}

	@Override
	public Void visitExclusiveOrExpression(CParser.ExclusiveOrExpressionContext ctx) {
		ctx.andExpression(0).accept(this);
		Boolean b = ctx.andExpression().size() > 1;
		if(b) {
			if(bitwiseOption==BitwiseOption.INTEGER) bitwiseOption = BitwiseOption.BITWISE;
		}
		return null;
	}

	@Override
	public Void visitAndExpression(CParser.AndExpressionContext ctx) {
		ctx.equalityExpression(0).accept(this);
		Boolean b = ctx.equalityExpression().size() > 1;
		if(b) {
			if(bitwiseOption==BitwiseOption.INTEGER) bitwiseOption = BitwiseOption.BITWISE;
		}
		return null;
	}

	@Override
	public Void visitShiftExpression(CParser.ShiftExpressionContext ctx) {
		ctx.additiveExpression(0).accept(this);
		Boolean b = ctx.additiveExpression().size() > 1;
		if(b) {
			if(bitwiseOption==BitwiseOption.INTEGER) bitwiseOption = BitwiseOption.BITWISE;
		}
		return null;
	}

}