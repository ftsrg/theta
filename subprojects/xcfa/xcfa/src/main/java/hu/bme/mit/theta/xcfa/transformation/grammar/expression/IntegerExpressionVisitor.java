package hu.bme.mit.theta.xcfa.transformation.grammar.expression;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvAndExpr;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvOrExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.bvtype.BvXorExpr;
import hu.bme.mit.theta.xcfa.dsl.gen.CParser;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.transformation.grammar.function.FunctionVisitor;
import hu.bme.mit.theta.xcfa.transformation.grammar.type.TypeVisitor;
import hu.bme.mit.theta.xcfa.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.xcfa.transformation.model.statements.CAssignment;
import hu.bme.mit.theta.xcfa.transformation.model.statements.CCall;
import hu.bme.mit.theta.xcfa.transformation.model.statements.CExpr;
import hu.bme.mit.theta.xcfa.transformation.model.statements.CStatement;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CComplexType;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class IntegerExpressionVisitor extends ExpressionVisitor {
	public IntegerExpressionVisitor(Deque<Map<String, VarDecl<?>>> variables, Map<VarDecl<?>, CDeclaration> functions) {
		super(variables, functions);
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
			Expr<?> expr = ctx.logicalOrExpression().accept(this);
			Expr<?> lhs = ifTrue.getExpression();
			Expr<?> rhs = ctx.conditionalExpression().accept(this);
			CComplexType smallestCommonType = CComplexType.getSmallestCommonType(List.of(CComplexType.getType(lhs), CComplexType.getType(rhs)));
			IteExpr<?> ite = Ite(
					AbstractExprs.Neq(CComplexType.getType(expr).getNullValue(), expr),
					smallestCommonType.castTo(lhs),
					smallestCommonType.castTo(rhs)
			);
			XcfaMetadata.create(ite, "cType", smallestCommonType);
			return ite;
		}
		else return ctx.logicalOrExpression().accept(this);
	}

	@Override
	public Expr<?> visitLogicalOrExpression(CParser.LogicalOrExpressionContext ctx) {
		if(ctx.logicalAndExpression().size() > 1) {
			List<Expr<BoolType>> collect = ctx.logicalAndExpression().stream().map(logicalAndExpressionContext -> {
					Expr<?> expr = logicalAndExpressionContext.accept(this);
					return AbstractExprs.Neq(CComplexType.getType(expr).getNullValue(), expr);
			}).collect(Collectors.toList());
			CComplexType signedInt = CComplexType.getSignedInt();
			IteExpr<?> ite = Ite(BoolExprs.Or(collect), signedInt.getUnitValue(), signedInt.getNullValue());
			XcfaMetadata.create(ite, "cType", signedInt);
			return ite;
		}
		return ctx.logicalAndExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitLogicalAndExpression(CParser.LogicalAndExpressionContext ctx) {
		if(ctx.inclusiveOrExpression().size() > 1) {
			List<Expr<BoolType>> collect = ctx.inclusiveOrExpression().stream().map(inclusiveOrExpression -> {
				Expr<?> expr = inclusiveOrExpression.accept(this);
				return AbstractExprs.Neq(CComplexType.getType(expr).getNullValue(), expr);
			}).collect(Collectors.toList());
			CComplexType signedInt = CComplexType.getSignedInt();
			IteExpr<?> ite = Ite(BoolExprs.And(collect), signedInt.getUnitValue(), signedInt.getNullValue());
			XcfaMetadata.create(ite, "cType", signedInt);
			return ite;
		}
		return ctx.inclusiveOrExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitInclusiveOrExpression(CParser.InclusiveOrExpressionContext ctx) {
		if(ctx.exclusiveOrExpression().size() > 1) {
			List<Expr<?>> exprs = ctx.exclusiveOrExpression().stream().map(exclusiveOrExpression -> exclusiveOrExpression.accept(this)).collect(Collectors.toList());
			List<CComplexType> types = exprs.stream().map(CComplexType::getType).collect(Collectors.toList());
			CComplexType smallestCommonType = CComplexType.getSmallestCommonType(types);
			List<Expr<BvType>> collect = exprs.stream().map(expr -> {
				Expr<?> ret = smallestCommonType.castTo(expr);
				checkState(ret.getType() instanceof BvType, "Non-bitvector type found!");
				//noinspection unchecked
				return (Expr<BvType>)ret;
			}).collect(Collectors.toList());
			BvOrExpr or = BvExprs.Or(collect);
			XcfaMetadata.create(or, "cType", smallestCommonType);
			return or;
		}
		return ctx.exclusiveOrExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitExclusiveOrExpression(CParser.ExclusiveOrExpressionContext ctx) {
		if(ctx.andExpression().size() > 1) {
			List<Expr<?>> exprs = ctx.andExpression().stream().map(andExpression -> andExpression.accept(this)).collect(Collectors.toList());
			List<CComplexType> types = exprs.stream().map(CComplexType::getType).collect(Collectors.toList());
			CComplexType smallestCommonType = CComplexType.getSmallestCommonType(types);
			List<Expr<BvType>> collect = exprs.stream().map(expr -> {
				Expr<?> ret = smallestCommonType.castTo(expr);
				checkState(ret.getType() instanceof BvType, "Non-bitvector type found!");
				//noinspection unchecked
				return (Expr<BvType>)ret;
			}).collect(Collectors.toList());
			BvXorExpr xor = BvExprs.Xor(collect);
			XcfaMetadata.create(xor, "cType", smallestCommonType);
			return xor;
		}
		return ctx.andExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitAndExpression(CParser.AndExpressionContext ctx) {
		if(ctx.equalityExpression().size() > 1) {
			List<Expr<?>> exprs = ctx.equalityExpression().stream().map(equalityExpression -> equalityExpression.accept(this)).collect(Collectors.toList());
			List<CComplexType> types = exprs.stream().map(CComplexType::getType).collect(Collectors.toList());
			CComplexType smallestCommonType = CComplexType.getSmallestCommonType(types);
			List<Expr<BvType>> collect = exprs.stream().map(expr -> {
				Expr<?> ret = smallestCommonType.castTo(expr);
				checkState(ret.getType() instanceof BvType, "Non-bitvector type found!");
				//noinspection unchecked
				return (Expr<BvType>)ret;
			}).collect(Collectors.toList());
			BvAndExpr and = BvExprs.And(collect);
			XcfaMetadata.create(and, "cType", smallestCommonType);
			return and;
		}
		return ctx.equalityExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitEqualityExpression(CParser.EqualityExpressionContext ctx) {
		if(ctx.relationalExpression().size() > 1) {
			Expr<?> expr = null;
			for(int i = 0; i < ctx.relationalExpression().size() - 1; ++i) {
				Expr<?> leftOp, rightOp;
				if(expr == null)
					leftOp = ctx.relationalExpression(i).accept(this);
				else
					leftOp = expr;
				rightOp = ctx.relationalExpression(i+1).accept(this);
				CComplexType smallestCommonType = CComplexType.getSmallestCommonType(List.of(CComplexType.getType(leftOp), CComplexType.getType(rightOp)));
				Expr<?> leftExpr = smallestCommonType.castTo(leftOp);
				Expr<?> rightExpr = smallestCommonType.castTo(rightOp);
				CComplexType signedInt = CComplexType.getSignedInt();
				expr = Ite(AbstractExprs.Eq(leftExpr, rightExpr), signedInt.getUnitValue(), signedInt.getNullValue());
				XcfaMetadata.create(expr, "cType", signedInt);
			}
			return expr;
		}
		return ctx.relationalExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitRelationalExpression(CParser.RelationalExpressionContext ctx) {
		if(ctx.shiftExpression().size() > 1) {
			Expr<?> expr = null;
			for(int i = 0; i < ctx.shiftExpression().size() - 1; ++i) {
				Expr<?> leftOp, rightOp;
				if(expr == null)
					leftOp = ctx.shiftExpression(i).accept(this);
				else
					leftOp = expr;
				rightOp = ctx.shiftExpression(i+1).accept(this);
				CComplexType smallestCommonType = CComplexType.getSmallestCommonType(List.of(CComplexType.getType(leftOp), CComplexType.getType(rightOp)));
				Expr<?> leftExpr = smallestCommonType.castTo(leftOp);
				Expr<?> rightExpr = smallestCommonType.castTo(rightOp);
				Expr<BoolType> guard;
				switch(ctx.signs.get(i).getText()) {
					case "<": guard = AbstractExprs.Lt(leftExpr, rightExpr); break;
					case ">": guard = AbstractExprs.Gt(leftExpr, rightExpr); break;
					case "<=": guard = AbstractExprs.Leq(leftExpr, rightExpr); break;
					case ">=": guard = AbstractExprs.Geq(leftExpr, rightExpr); break;
					default:
						throw new IllegalStateException("Unexpected value: " + ctx.signs.get(i).getText());
				}
				CComplexType signedInt = CComplexType.getSignedInt();
				expr = Ite(guard, signedInt.getUnitValue(), signedInt.getNullValue());
				XcfaMetadata.create(expr, "cType", signedInt);
			}
			return expr;
		}
		return ctx.shiftExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitShiftExpression(CParser.ShiftExpressionContext ctx) {
		if(ctx.additiveExpression().size() > 1) {
			Expr<?> accept = ctx.additiveExpression(0).accept(this);
			checkState(accept.getType() instanceof BvType);
			//noinspection unchecked
			Expr<BvType> expr = (Expr<BvType>) accept;
			CComplexType smallestCommonType = CComplexType.getSmallestCommonType(List.of(CComplexType.getType(expr)));
			checkState(smallestCommonType.getSmtType() instanceof BvType);
			for(int i = 1; i < ctx.additiveExpression().size(); ++i) {
				Expr<BvType> rightOp;
				accept = ctx.additiveExpression(i).accept(this);
				checkState(accept.getType() instanceof BvType);
				//noinspection unchecked
				rightOp = (Expr<BvType>) accept;
				Expr<BvType> leftExpr = cast(smallestCommonType.castTo(expr), (BvType)smallestCommonType.getSmtType());
				Expr<BvType> rightExpr = cast(smallestCommonType.castTo(rightOp), (BvType)smallestCommonType.getSmtType());
				expr = BvExprs.ShiftLeft(leftExpr, rightExpr);
				XcfaMetadata.create(expr, "cType", smallestCommonType);
			}
			return expr;
		}
		return ctx.additiveExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitAdditiveExpression(CParser.AdditiveExpressionContext ctx) {
		if(ctx.multiplicativeExpression().size() > 1) {
			List<Expr<?>> exprs = ctx.multiplicativeExpression().stream().map(multiplicativeExpression -> multiplicativeExpression.accept(this)).collect(Collectors.toList());
			List<CComplexType> types = exprs.stream().map(CComplexType::getType).collect(Collectors.toList());
			CComplexType smallestCommonType = CComplexType.getSmallestCommonType(types);
			List<Expr<?>> collect = new ArrayList<>();
			for (int i = 0; i < exprs.size(); i++) {
				Expr<?> expr = (i == 0 || ctx.signs.get(i-1).getText().equals("+")) ? exprs.get(i) : AbstractExprs.Neg(exprs.get(i));
				Expr<?> castTo = smallestCommonType.castTo(expr);
				collect.add(castTo);
			}
			Expr<?> add = AbstractExprs.Add(collect);
			add = smallestCommonType.castTo(add);
			XcfaMetadata.create(add, "cType", smallestCommonType);
			return add;
		}
		return ctx.multiplicativeExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitMultiplicativeExpression(CParser.MultiplicativeExpressionContext ctx) {
		if(ctx.castExpression().size() > 1) {
			Expr<?> expr = null;
			for(int i = 0; i < ctx.castExpression().size() - 1; ++i) {
				Expr<?> leftOp, rightOp;
				if(expr == null)
					leftOp = ctx.castExpression(i).accept(this);
				else
					leftOp = expr;
				rightOp = ctx.castExpression(i+1).accept(this);
				CComplexType smallestCommonType = CComplexType.getSmallestCommonType(List.of(CComplexType.getType(leftOp), CComplexType.getType(rightOp)));
				Expr<?> leftExpr = smallestCommonType.castTo(leftOp);
				Expr<?> rightExpr = smallestCommonType.castTo(rightOp);
				switch(ctx.signs.get(i).getText()) {
					case "*": expr = AbstractExprs.Mul(leftExpr, rightExpr); break;
					case "/": expr = AbstractExprs.Div(leftExpr, rightExpr); break;
					case "%": expr = AbstractExprs.Rem(leftExpr, rightExpr); break;
					default:
						throw new IllegalStateException("Unexpected value: " + ctx.signs.get(i).getText());
				}
				expr = smallestCommonType.castTo(expr);
				XcfaMetadata.create(expr, "cType", smallestCommonType);
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
		CComplexType actualType = ctx.typeName().specifierQualifierList().accept(TypeVisitor.instance).getActualType();
		Expr<?> expr = actualType.castTo(ctx.castExpression().accept(this));
		expr = actualType.castTo(expr);
		XcfaMetadata.create(expr, "cType", actualType);
		return expr;
	}

	@Override
	public Expr<?> visitUnaryExpression(CParser.UnaryExpressionContext ctx) {
		checkState(ctx.unaryExpressionSizeOrAlignOf() == null, "Sizeof and alignof are not yet implemented");
		Expr<?> ret = ctx.unaryExpressionCast() == null ? ctx.postfixExpression().accept(this) : ctx.unaryExpressionCast().accept(this);
		int increment = ctx.unaryExpressionIncrement().size() - ctx.unaryExpressionDecrement().size();
		if(increment != 0) {
			Expr<?> expr = ret;
			CComplexType type = CComplexType.getType(ret);
			for (int i = 0; i < Math.abs(increment); i++) {
				if(increment < 0)
					expr = AbstractExprs.Sub(expr, type.getUnitValue());
				else
					expr = AbstractExprs.Add(expr, type.getUnitValue());
			}
			expr = type.castTo(expr);
			XcfaMetadata.create(expr, "cType", type);
			Expr<?> wrappedExpr = type.castTo(expr);
			CExpr cexpr = new CExpr(wrappedExpr);
			CAssignment cAssignment = new CAssignment(ret, cexpr, "=");
			preStatements.add(cAssignment);
			FunctionVisitor.instance.recordMetadata(ctx, cAssignment);
			FunctionVisitor.instance.recordMetadata(ctx, cexpr);
		}
		return ret;
	}

	@Override
	public Expr<?> visitUnaryExpressionCast(CParser.UnaryExpressionCastContext ctx) {
		Expr<?> accept = ctx.castExpression().accept(this);
		switch(ctx.unaryOperator().getText()) {
			case "-": {
				Expr<?> negExpr = AbstractExprs.Neg(accept);
				CComplexType type = CComplexType.getType(accept);
				negExpr = type.castTo(negExpr);
				XcfaMetadata.create(negExpr, "cType", type);
				return negExpr;
			}
			case "+": return accept; // no need to update type, it remains the same
			case "!":
				CComplexType signedInt = CComplexType.getSignedInt();
				accept = Ite(Eq(accept, CComplexType.getType(accept).getNullValue()), signedInt.getUnitValue(), signedInt.getNullValue());
				XcfaMetadata.create(accept, "cType", signedInt);
				return accept;
			case "~":
				checkState(accept.getType() instanceof BvType);
				//noinspection unchecked
				Expr<?> expr = BvExprs.Neg((Expr<BvType>) accept);
				CComplexType type = CComplexType.getType(accept);
				expr = type.castTo(expr);
				XcfaMetadata.create(expr, "cType", type);
				return expr;
			case "*":
			case "&": throw new UnsupportedOperationException("Pointers are not yet supported!");
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
			// we handle ++ and -- as if they were additions and assignments
			int increment = ctx.postfixExpressionIncrement().size() - ctx.postfixExpressionDecrement().size();
			if(increment != 0) {
				Expr<?> expr = primary;
				CComplexType type = CComplexType.getType(primary);
				for (int i = 0; i < Math.abs(increment); i++) {
					if(increment < 0)
						expr = AbstractExprs.Sub(expr, type.getUnitValue());
					else
						expr = AbstractExprs.Add(expr, type.getUnitValue());
				}
				expr = type.castTo(expr);
				XcfaMetadata.create(expr, "cType", type);
				CExpr cexpr;
				cexpr = new CExpr(expr);
				// no need to truncate here, as left and right side types are the same
				CAssignment cAssignment = new CAssignment(primary, cexpr, "=");
				postStatements.add(cAssignment);
				FunctionVisitor.instance.recordMetadata(ctx, cAssignment);
				FunctionVisitor.instance.recordMetadata(ctx, cexpr);
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
		String text = ctx.getText().toLowerCase();
		checkState(!text.endsWith("f"), "Constant cannot be a float");
		checkState(!text.contains("."), "Constant cannot be a double");

		boolean isLong = text.endsWith("l");
		if(isLong) text = text.substring(0, text.length() - 1);
		boolean isLongLong = text.endsWith("l");
		if(isLongLong) text = text.substring(0, text.length() - 1);
		boolean isUnsigned = text.endsWith("u");
		if(isUnsigned) text = text.substring(0, text.length() - 1);

		LitExpr<?> litExpr;
		if(text.startsWith("0x")) {
			long l = Long.parseLong(text.substring(2), 16);
			litExpr = Int(BigInteger.valueOf(l));
		}
		else if (text.startsWith("0b")) {
			long l = Long.parseLong(text.substring(2), 2);
			litExpr = Int(BigInteger.valueOf(l));
		}
		else if (text.startsWith("0") && text.length() > 1) {
			long l = Long.parseLong(text.substring(1), 8);
			litExpr = Int(BigInteger.valueOf(l));
		}
		else {
			long l = Long.parseLong(text, 10);
			litExpr = Int(BigInteger.valueOf(l));
		}

		CComplexType type;
		if(isLongLong && isUnsigned) type = CComplexType.getUnsignedLongLong();
		else if(isLongLong) type = CComplexType.getSignedLongLong();
		else if(isLong && isUnsigned) type = CComplexType.getUnsignedLong();
		else if(isLong) type = CComplexType.getSignedLong();
		else if(isUnsigned) type = CComplexType.getUnsignedInt();
		else type = CComplexType.getSignedInt();

		XcfaMetadata.create(litExpr, "cType", type);
		return litExpr;

	}

	@Override
	public Expr<?> visitPrimaryExpressionBraceExpression(CParser.PrimaryExpressionBraceExpressionContext ctx) {
		CStatement statement = ctx.expression().accept(FunctionVisitor.instance);
	 	preStatements.add(statement);
	    return statement.getExpression();
	}

	@Override
	public Expr<?> visitPrimaryExpressionGccExtension(CParser.PrimaryExpressionGccExtensionContext ctx) {
		return null;
	}

	@Override
	public Expr<?> visitPrimaryExpressionStrings(CParser.PrimaryExpressionStringsContext ctx) {
		CComplexType signedInt = CComplexType.getSignedInt();
		Expr<?> ret = signedInt.getUnitValue();
		System.err.println("Warning: using int(1) as a string constant");
		XcfaMetadata.create(ret, "cType", signedInt);
		return ret;
	}


}
