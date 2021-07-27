package hu.bme.mit.theta.xcfa.transformation.grammar.preprocess;

import hu.bme.mit.theta.xcfa.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.xcfa.dsl.gen.CParser;

public class BitwiseChecker extends CBaseVisitor<Void> {
	public static final BitwiseChecker instance = new BitwiseChecker();
	private static boolean isBitwise = false;

	public boolean checkIfBitwise(CParser.CompilationUnitContext ctx) {
		isBitwise = false;
		ctx.accept(instance);
		return isBitwise;
	}

	@Override
	public Void visitTypeSpecifierDouble(CParser.TypeSpecifierDoubleContext ctx) {
		isBitwise = true;
		return null;
	}

	@Override
	public Void visitTypeSpecifierFloat(CParser.TypeSpecifierFloatContext ctx) {
		isBitwise = true;
		return null;
	}

	@Override
	public Void visitInclusiveOrExpression(CParser.InclusiveOrExpressionContext ctx) {
		ctx.exclusiveOrExpression(0).accept(this);
		Boolean b = ctx.exclusiveOrExpression().size() > 1;
		if(b) {
			isBitwise = true;
		}
		return null;
	}

	@Override
	public Void visitExclusiveOrExpression(CParser.ExclusiveOrExpressionContext ctx) {
		ctx.andExpression(0).accept(this);
		Boolean b = ctx.andExpression().size() > 1;
		if(b) {
			isBitwise = true;
		}
		return null;
	}

	@Override
	public Void visitAndExpression(CParser.AndExpressionContext ctx) {
		ctx.equalityExpression(0).accept(this);
		Boolean b = ctx.equalityExpression().size() > 1;
		if(b) {
			isBitwise = true;
		}
		return null;
	}

	@Override
	public Void visitShiftExpression(CParser.ShiftExpressionContext ctx) {
		ctx.additiveExpression(0).accept(this);
		Boolean b = ctx.additiveExpression().size() > 1;
		if(b) {
			isBitwise = true;
		}
		return null;
	}

}
