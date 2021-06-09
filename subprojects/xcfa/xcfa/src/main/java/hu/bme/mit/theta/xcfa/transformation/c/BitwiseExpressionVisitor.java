package hu.bme.mit.theta.xcfa.transformation.c;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.xcfa.dsl.gen.CParser;

import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;

public class BitwiseExpressionVisitor extends ExpressionVisitor {

	public BitwiseExpressionVisitor(Deque<Map<String, VarDecl<?>>> variables) {
		super(variables);
	}

	@Override
	public Expr<?> visitConditionalExpression(CParser.ConditionalExpressionContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitLogicalOrExpression(CParser.LogicalOrExpressionContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitLogicalAndExpression(CParser.LogicalAndExpressionContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitInclusiveOrExpression(CParser.InclusiveOrExpressionContext ctx) {
		if(ctx.exclusiveOrExpression().size() > 1) {
			List<? extends Expr<BvType>> collect = ctx.exclusiveOrExpression().stream().map(exclusiveOrExpressionContext -> {
				Expr<?> expr = exclusiveOrExpressionContext.accept(this);
				checkState(expr.getType() instanceof BvType);
				//noinspection unchecked
				return (Expr<BvType>)expr;
			}).collect(Collectors.toList());
			BvExprs.Or(collect);
		}
		return ctx.exclusiveOrExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitExclusiveOrExpression(CParser.ExclusiveOrExpressionContext ctx) {
		if(ctx.andExpression().size() > 1) {
			List<? extends Expr<BvType>> collect = ctx.andExpression().stream().map(exclusiveOrExpressionContext -> {
				Expr<?> expr = exclusiveOrExpressionContext.accept(this);
				checkState(expr.getType() instanceof BvType);
				//noinspection unchecked
				return (Expr<BvType>)expr;
			}).collect(Collectors.toList());
			BvExprs.Or(collect);
		}
		return ctx.andExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitAndExpression(CParser.AndExpressionContext ctx) {
		if(ctx.equalityExpression().size() > 1) {
			List<? extends Expr<BvType>> collect = ctx.equalityExpression().stream().map(exclusiveOrExpressionContext -> {
				Expr<?> expr = exclusiveOrExpressionContext.accept(this);
				checkState(expr.getType() instanceof BvType);
				//noinspection unchecked
				return (Expr<BvType>)expr;
			}).collect(Collectors.toList());
			BvExprs.Or(collect);
		}
		return ctx.equalityExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitEqualityExpression(CParser.EqualityExpressionContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitRelationalExpression(CParser.RelationalExpressionContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitShiftExpression(CParser.ShiftExpressionContext ctx) {
		if(ctx.additiveExpression().size() > 1) {
			throw new UnsupportedOperationException("not yet implemented for Bv!");
		}
		else return ctx.additiveExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitAdditiveExpression(CParser.AdditiveExpressionContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitMultiplicativeExpression(CParser.MultiplicativeExpressionContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitCastExpressionUnaryExpression(CParser.CastExpressionUnaryExpressionContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitCastExpressionCast(CParser.CastExpressionCastContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitCastExpressionDigitSequence(CParser.CastExpressionDigitSequenceContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitUnaryExpression(CParser.UnaryExpressionContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitUnaryExpressionCast(CParser.UnaryExpressionCastContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitPostfixExpression(CParser.PostfixExpressionContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitPrimaryExpressionId(CParser.PrimaryExpressionIdContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitPrimaryExpressionConstant(CParser.PrimaryExpressionConstantContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitPrimaryExpressionBraceExpression(CParser.PrimaryExpressionBraceExpressionContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitPrimaryExpressionGccExtension(CParser.PrimaryExpressionGccExtensionContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitPrimaryExpressionStrings(CParser.PrimaryExpressionStringsContext ctx) {
		return null;
	}

}
