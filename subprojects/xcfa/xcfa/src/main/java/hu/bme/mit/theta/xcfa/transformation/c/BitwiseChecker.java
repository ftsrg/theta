package hu.bme.mit.theta.xcfa.transformation.c;

import hu.bme.mit.theta.xcfa.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.xcfa.dsl.gen.CParser;
import hu.bme.mit.theta.xcfa.transformation.c.declaration.CDeclaration;
import org.antlr.v4.runtime.Token;

import java.util.List;

public class BitwiseChecker extends CBaseVisitor<Boolean> {
	public static final BitwiseChecker instance = new BitwiseChecker();

	@Override
	public Boolean visitInclusiveOrExpression(CParser.InclusiveOrExpressionContext ctx) {
		Boolean accept = ctx.exclusiveOrExpression(0).accept(this);
		return ctx.exclusiveOrExpression().size() > 1 || accept == null || accept;
	}

	@Override
	public Boolean visitExclusiveOrExpression(CParser.ExclusiveOrExpressionContext ctx) {
		Boolean accept = ctx.andExpression(0).accept(this);
		return ctx.andExpression().size() > 1 || accept == null || accept;
	}

	@Override
	public Boolean visitLogicalAndExpression(CParser.LogicalAndExpressionContext ctx) {
		Boolean accept = ctx.inclusiveOrExpression(0).accept(this);
		return ctx.inclusiveOrExpression().size() > 1 || accept == null || accept;
	}

	@Override
	public Boolean visitShiftExpression(CParser.ShiftExpressionContext ctx) {
		Boolean accept = ctx.additiveExpression(0).accept(this);
		return ctx.additiveExpression().size() > 1 || accept == null || accept;

	}

}
