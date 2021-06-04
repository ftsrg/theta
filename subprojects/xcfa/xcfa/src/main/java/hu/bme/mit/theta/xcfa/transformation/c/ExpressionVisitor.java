package hu.bme.mit.theta.xcfa.transformation.c;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
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
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Div;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Gt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Leq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mul;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neg;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Rem;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class ExpressionVisitor extends CBaseVisitor<Expr<?>> {
	private final List<CStatement> preStatements = new ArrayList<>();
	private final List<CStatement> postStatements = new ArrayList<>();
	private final Deque<Map<String, VarDecl<?>>> variables;

	private static boolean isBitwiseOps = false;

	public ExpressionVisitor(Deque<Map<String, VarDecl<?>>> variables) {
		this.variables = variables;
	}
	
	private VarDecl<?> getVar(String name) {
		for (Map<String, VarDecl<?>> variableList : variables) {
			if(variableList.containsKey(name)) return variableList.get(name);
		}
		throw new RuntimeException("No such variable: " + name);
	}

	public static void setBitwise(Boolean bitwise) {
		checkState(bitwise == null || !bitwise, "Bitwise ops not yet implemented!");
		isBitwiseOps = bitwise != null;
	}

	private Expr<BvType> checkAndGetBvType(Expr<?> expr) {
		checkState(expr.getType() instanceof BvType);
		//noinspection unchecked
		return (Expr<BvType>) expr;
	}

	@Override
	public Expr<?> visitConditionalExpression(CParser.ConditionalExpressionContext ctx) {
		if(ctx.expression() != null) {
			CStatement ifTrue = ctx.expression().accept(FunctionVisitor.instance);
			if(ifTrue instanceof CAssignment) {
				preStatements.add(ifTrue);
			}
			return Ite(
					Neq(Int(0),
							cast(ctx.logicalOrExpression().accept(this), Int())),
					ifTrue.getExpression(),
					ctx.conditionalExpression().accept(this)
					);
		}
		else return ctx.logicalOrExpression().accept(this);
	}

	@Override
	public Expr<?> visitLogicalOrExpression(CParser.LogicalOrExpressionContext ctx) {
		if(ctx.logicalAndExpression().size() > 1) {
			List<Expr<BoolType>> collect = ctx.logicalAndExpression().stream().map(logicalAndExpressionContext ->
					Neq(Int(0), cast(logicalAndExpressionContext.accept(this), Int()))).
					collect(Collectors.toList());
			return Ite(BoolExprs.Or(collect), Int(1), Int(0));
		}
		return ctx.logicalAndExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitLogicalAndExpression(CParser.LogicalAndExpressionContext ctx) {
		if(ctx.inclusiveOrExpression().size() > 1) {
			List<Expr<BoolType>> collect = ctx.inclusiveOrExpression().stream().map(inclusiveOrExpressionContext ->
					Neq(Int(0), cast(inclusiveOrExpressionContext.accept(this), Int()))).
					collect(Collectors.toList());
			return Ite(BoolExprs.And(collect), Int(1), Int(0));
		}
		return ctx.inclusiveOrExpression(0).accept(this);
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
		if(ctx.relationalExpression().size() > 1) {
			Expr<IntType> expr = null;
			for(int i = 0; i < ctx.relationalExpression().size() - 1; ++i) {
				Expr<IntType> leftOp, rightOp;
				if(expr == null)
					leftOp = cast(ctx.relationalExpression(i).accept(this), Int());
				else
					leftOp = expr;
				rightOp = cast(ctx.relationalExpression(i+1).accept(this), Int());
				expr = cast(Ite(
						ctx.signs.get(i).getText().equals("==") ? IntExprs.Eq(leftOp, rightOp) : IntExprs.Neq(leftOp, rightOp),
						Int(1),
						Int(0)
				), Int());
			}
			return expr;
		}
		return ctx.relationalExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitRelationalExpression(CParser.RelationalExpressionContext ctx) {
		if(ctx.shiftExpression().size() > 1) {
			Expr<IntType> expr = null;
			for(int i = 0; i < ctx.shiftExpression().size() - 1; ++i) {
				Expr<IntType> leftOp, rightOp;
				if(expr == null)
					leftOp = cast(ctx.shiftExpression(i).accept(this), Int());
				else
					leftOp = expr;
				rightOp = cast(ctx.shiftExpression(i+1).accept(this), Int());
				Expr<BoolType> guard = null;
				switch(ctx.signs.get(i).getText()) {
					case "<": guard = Lt(leftOp, rightOp); break;
					case ">": guard = Gt(leftOp, rightOp); break;
					case "<=": guard = Leq(leftOp, rightOp); break;
					case ">=": guard = Geq(leftOp, rightOp); break;
				}
				expr = cast(Ite(
						guard,
						Int(1),
						Int(0)
				), Int());
			}
			return expr;
		}
		return ctx.shiftExpression(0).accept(this);
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
		if(ctx.multiplicativeExpression().size() > 1) {
			List<Expr<IntType>> arguments = new ArrayList<>();
			for(int i = 0; i < ctx.multiplicativeExpression().size(); ++i) {
				if(i == 0 || ctx.signs.get(i-1).getText().equals("+")) arguments.add(cast(ctx.multiplicativeExpression(i).accept(this),Int()));
				else arguments.add(Neg(cast(ctx.multiplicativeExpression(i).accept(this),Int())));
			}
			return Add(arguments);
		}
		return ctx.multiplicativeExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitMultiplicativeExpression(CParser.MultiplicativeExpressionContext ctx) {
		if(ctx.castExpression().size() > 1) {
			Expr<IntType> expr = null;
			for(int i = 0; i < ctx.castExpression().size() - 1; ++i) {
				Expr<IntType> leftOp, rightOp;
				if(expr == null)
					leftOp = cast(ctx.castExpression(i).accept(this), Int());
				else
					leftOp = expr;
				rightOp = cast(ctx.castExpression(i+1).accept(this), Int());
				switch(ctx.signs.get(i).getText()) {
					case "*": expr = Mul(leftOp, rightOp); break;
					case "/": expr = Div(leftOp, rightOp); break;
					case "%": expr = Rem(leftOp, rightOp); break;
				}
			}
			return expr;
		}
		return ctx.castExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitCastExpressionUnaryExpression(CParser.CastExpressionUnaryExpressionContext ctx) {
		return ctx.unaryExpression().accept(this);
	}

	@Override
	public Expr<?> visitCastExpressionCast(CParser.CastExpressionCastContext ctx) {
		return ctx.castExpression().accept(this);
	}

	@Override
	public Expr<?> visitCastExpressionDigitSequence(CParser.CastExpressionDigitSequenceContext ctx) {
		return Int(Integer.parseInt(ctx.getText()));
	}

	@Override
	public Expr<?> visitUnaryExpression(CParser.UnaryExpressionContext ctx) {
		checkState(ctx.unaryExpressionSizeOrAlignOf() == null, "Sizeof and alignof are not yet implemented");
		Expr<?> ret = ctx.unaryExpressionCast() == null ? ctx.postfixExpression().accept(this) : ctx.unaryExpressionCast().accept(this);
		int increment = ctx.unaryExpressionIncrement().size() - ctx.unaryExpressionDecrement().size();
		if(increment != 0) {
			CAssignment cAssignment = new CAssignment(ret, new CExpr(Add(cast(ret, Int()), Int(increment))), "=");
			preStatements.add(cAssignment);
			FunctionVisitor.instance.recordMetadata(ctx, cAssignment);
		}
		return ret;
	}

	@Override
	public Expr<?> visitUnaryExpressionCast(CParser.UnaryExpressionCastContext ctx) {
		Expr<?> accept = ctx.castExpression().accept(this);
		switch(ctx.unaryOperator().getText()) {
			case "-": return Neg(cast(accept, Int()));
			case "+": return accept;
			case "!": return Ite(Eq(cast(accept, Int()), Int(0)), Int(1), Int(0));
		}
		return accept;
	}

	@Override
	public Expr<?> visitPostfixExpression(CParser.PostfixExpressionContext ctx) {
		checkState(ctx.postfixExpressionBrackets().size() == 0, "Arrays are not yet supported!");
		checkState(ctx.postfixExpressionMemberAccess().size() == 0, "Structs are not yet supported!");
		checkState(ctx.postfixExpressionPtrMemberAccess().size() == 0, "Structs are not yet supported!");
		if(ctx.postfixExpressionBraces().size() == 1) {
			CParser.ArgumentExpressionListContext exprList = ctx.postfixExpressionBraces(0).argumentExpressionList();
			List<CStatement> arguments = exprList == null ? List.of() : exprList.assignmentExpression().stream().map(assignmentExpressionContext -> assignmentExpressionContext.accept(FunctionVisitor.instance)).collect(Collectors.toList());
			CCall cCall = new CCall(ctx.primaryExpression().getText(), arguments);
			preStatements.add(cCall);
			FunctionVisitor.instance.recordMetadata(ctx, cCall);
			return cCall.getRet().getRef();
		}
		else {
			Expr<?> primary = ctx.primaryExpression().accept(this);
			int increment = ctx.postfixExpressionIncrement().size() - ctx.postfixExpressionDecrement().size();
			if(increment != 0) {
				CAssignment cAssignment = new CAssignment(primary, new CExpr(Add(cast(primary, Int()), Int(increment))), "=");
				postStatements.add(cAssignment);
				FunctionVisitor.instance.recordMetadata(ctx, cAssignment);
			}
			return primary;
		}
	}

	@Override
	public Expr<?> visitPrimaryExpressionId(CParser.PrimaryExpressionIdContext ctx) {
		return getVar(ctx.Identifier().getText()).getRef();
	}

	@Override
	public Expr<?> visitPrimaryExpressionConstant(CParser.PrimaryExpressionConstantContext ctx) {
		return IntLitExpr.of(new BigInteger(ctx.getText().replaceAll("[LUlu]", "")));
	}

	@Override
	public Expr<?> visitPrimaryExpressionBraceExpression(CParser.PrimaryExpressionBraceExpressionContext ctx) {
		System.err.println("Brace expression not fully implemented: " + ctx.getText());
		return ctx.expression().accept(FunctionVisitor.instance).getExpression();
	}

	@Override
	public Expr<?> visitPrimaryExpressionGccExtension(CParser.PrimaryExpressionGccExtensionContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitPrimaryExpressionStrings(CParser.PrimaryExpressionStringsContext ctx) {
		return Int(-1);
	}

	public List<CStatement> getPostStatements() {
		return postStatements;
	}

	public List<CStatement> getPreStatements() {
		return preStatements;
	}
}
