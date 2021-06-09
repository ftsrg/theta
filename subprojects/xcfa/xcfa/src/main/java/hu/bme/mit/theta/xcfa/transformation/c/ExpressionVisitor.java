package hu.bme.mit.theta.xcfa.transformation.c;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatExprs;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.xcfa.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.xcfa.dsl.gen.CParser;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CAssignment;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CCall;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CExpr;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CStatement;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public abstract class ExpressionVisitor extends CBaseVisitor<Expr<?>> {
	protected final List<CStatement> preStatements = new ArrayList<>();
	protected final List<CStatement> postStatements = new ArrayList<>();
	protected final Deque<Map<String, VarDecl<?>>> variables;
	protected static boolean isBitwiseOps = false;

	protected ExpressionVisitor(Deque<Map<String, VarDecl<?>>> variables) {
		this.variables = variables;
	}

	public static ExpressionVisitor create(Deque<Map<String, VarDecl<?>>> variables) {
		if(isBitwiseOps) {
			return new BitwiseExpressionVisitor(variables);
		} else {
			return new IntegerExpressionVisitor(variables);
		}
	}

	protected VarDecl<?> getVar(String name) {
		for (Map<String, VarDecl<?>> variableList : variables) {
			if(variableList.containsKey(name)) return variableList.get(name);
		}
		throw new RuntimeException("No such variable: " + name);
	}

	public static void setBitwise(Boolean bitwise) {
		// TODO remove this check
		checkState(bitwise == null || !bitwise, "Bitwise ops not yet implemented!");
		isBitwiseOps = bitwise != null;
	}

	public List<CStatement> getPostStatements() {
		return postStatements;
	}

	public List<CStatement> getPreStatements() {
		return preStatements;
	}

	@Override
	public abstract Expr<?> visitConditionalExpression(CParser.ConditionalExpressionContext ctx);

	@Override
	public abstract Expr<?> visitLogicalOrExpression(CParser.LogicalOrExpressionContext ctx);

	@Override
	public abstract Expr<?> visitLogicalAndExpression(CParser.LogicalAndExpressionContext ctx);

	@Override
	public abstract Expr<?> visitInclusiveOrExpression(CParser.InclusiveOrExpressionContext ctx);

	@Override
	public abstract Expr<?> visitExclusiveOrExpression(CParser.ExclusiveOrExpressionContext ctx);

	@Override
	public abstract Expr<?> visitAndExpression(CParser.AndExpressionContext ctx);

	@Override
	public abstract Expr<?> visitEqualityExpression(CParser.EqualityExpressionContext ctx);

	@Override
	public abstract Expr<?> visitRelationalExpression(CParser.RelationalExpressionContext ctx);

	@Override
	public abstract Expr<?> visitShiftExpression(CParser.ShiftExpressionContext ctx);

	@Override
	public abstract Expr<?> visitAdditiveExpression(CParser.AdditiveExpressionContext ctx);

	@Override
	public abstract Expr<?> visitMultiplicativeExpression(CParser.MultiplicativeExpressionContext ctx);

	@Override
	public abstract Expr<?> visitCastExpressionUnaryExpression(CParser.CastExpressionUnaryExpressionContext ctx);

	@Override
	public abstract Expr<?> visitCastExpressionCast(CParser.CastExpressionCastContext ctx);

	@Override
	public abstract Expr<?> visitCastExpressionDigitSequence(CParser.CastExpressionDigitSequenceContext ctx);

	@Override
	public abstract Expr<?> visitUnaryExpression(CParser.UnaryExpressionContext ctx);

	@Override
	public abstract Expr<?> visitUnaryExpressionCast(CParser.UnaryExpressionCastContext ctx);

	@Override
	public abstract Expr<?> visitPostfixExpression(CParser.PostfixExpressionContext ctx);

	@Override
	public abstract Expr<?> visitPrimaryExpressionId(CParser.PrimaryExpressionIdContext ctx);

	@Override
	public abstract Expr<?> visitPrimaryExpressionConstant(CParser.PrimaryExpressionConstantContext ctx);

	@Override
	public abstract Expr<?> visitPrimaryExpressionBraceExpression(CParser.PrimaryExpressionBraceExpressionContext ctx);

	@Override
	public abstract Expr<?> visitPrimaryExpressionGccExtension(CParser.PrimaryExpressionGccExtensionContext ctx);

	@Override
	public abstract Expr<?> visitPrimaryExpressionStrings(CParser.PrimaryExpressionStringsContext ctx);

	public static Expr<?> getZeroLiteral(Type type) {
		if(type instanceof BoolType) {
			return FalseExpr.getInstance();
		} else if(type instanceof IntType) {
			return Int(0);
		} else if(type instanceof RatType) {
			return RatExprs.Rat(0,1);
		} else if(type instanceof ArrayType) {
			throw new RuntimeException("Zero literal of arrays in ExpressionVisitor not implemented yet");
		} else {
			throw new RuntimeException("Could not interpret type " + type);
		}
	}
}
