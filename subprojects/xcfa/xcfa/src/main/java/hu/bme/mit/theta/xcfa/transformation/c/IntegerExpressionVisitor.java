package hu.bme.mit.theta.xcfa.transformation.c;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.inttype.IntAddExpr;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntMulExpr;
import hu.bme.mit.theta.core.type.inttype.IntNegExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.xcfa.CIntTypeUtils;
import hu.bme.mit.theta.xcfa.dsl.gen.CParser;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.transformation.c.declaration.CDeclaration;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CAssignment;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CCall;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CExpr;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CStatement;
import hu.bme.mit.theta.xcfa.transformation.c.types.CType;
import hu.bme.mit.theta.xcfa.transformation.c.types.NamedType;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;
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
import static hu.bme.mit.theta.xcfa.transformation.c.types.CTypeFactory.NamedType;

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
			IteExpr<?> ite = Ite(
					Neq(Int(0),
							cast(expr, expr.getType())),
					ifTrue.getExpression(),
					ctx.conditionalExpression().accept(this)
			);
			XcfaMetadata.create(ite, "cType", NamedType.getInt());
			return ite;
		}
		else return ctx.logicalOrExpression().accept(this);
	}

	@Override
	public Expr<?> visitLogicalOrExpression(CParser.LogicalOrExpressionContext ctx) {
		if(ctx.logicalAndExpression().size() > 1) {
			List<Expr<BoolType>> collect = ctx.logicalAndExpression().stream().map(logicalAndExpressionContext -> {
					Expr<?> expr = logicalAndExpressionContext.accept(this);
					return Neq(getZeroLiteral(expr.getType()), cast(expr, expr.getType())); }).
				collect(Collectors.toList());
			IteExpr<?> ite = Ite(BoolExprs.Or(collect), Int(1), Int(0));
			XcfaMetadata.create(ite, "cType", NamedType.getInt());
			return ite;
		}
		return ctx.logicalAndExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitLogicalAndExpression(CParser.LogicalAndExpressionContext ctx) {
		if(ctx.inclusiveOrExpression().size() > 1) {
			List<Expr<BoolType>> collect = ctx.inclusiveOrExpression().stream().map(inclusiveOrExpressionContext -> {
				Expr<?> expr = inclusiveOrExpressionContext.accept(this);
				return Neq(getZeroLiteral(expr.getType()), cast(expr, expr.getType())); }).
					collect(Collectors.toList());
			IteExpr<?> ite = Ite(BoolExprs.And(collect), Int(1), Int(0));
			XcfaMetadata.create(ite, "cType", NamedType.getInt());
			return ite;
		}
		return ctx.inclusiveOrExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitInclusiveOrExpression(CParser.InclusiveOrExpressionContext ctx) {
		if(ctx.exclusiveOrExpression().size() > 1) throw new RuntimeException("Inclusive or should be handled by BitwiseExpressionVisitor");
		else return ctx.exclusiveOrExpression().get(0).accept(this);
	}

	@Override
	public Expr<?> visitExclusiveOrExpression(CParser.ExclusiveOrExpressionContext ctx) {
		if(ctx.andExpression().size() > 1) throw new RuntimeException("Exclusive or should be handled by BitwiseExpressionVisitor");
		else return ctx.andExpression().get(0).accept(this);
	}

	@Override
	public Expr<?> visitAndExpression(CParser.AndExpressionContext ctx) {
		if(ctx.equalityExpression().size() > 1) throw new RuntimeException("Bitwise and should be handled by BitwiseExpressionVisitor");
		else return ctx.equalityExpression().get(0).accept(this);
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
				Tuple2<Expr<IntType>, Expr<IntType>> exprTuple2 = CIntTypeUtils.castToCommonType(leftOp, rightOp);
				Expr<IntType> leftExpr = exprTuple2.get1();
				Expr<IntType> rightExpr = exprTuple2.get2();
				expr = cast(Ite(
						ctx.signs.get(i).getText().equals("==") ? IntExprs.Eq(leftExpr, rightExpr) : IntExprs.Neq(leftOp, rightOp),
						Int(1),
						Int(0)
				), Int());
				XcfaMetadata.create(expr, "cType", NamedType.getInt());
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
				Tuple2<Expr<IntType>, Expr<IntType>> exprTuple2 = CIntTypeUtils.castToCommonType(leftOp, rightOp);
				Expr<IntType> leftExpr = exprTuple2.get1();
				Expr<IntType> rightExpr = exprTuple2.get2();
				switch(ctx.signs.get(i).getText()) {
					case "<": guard = Lt(leftExpr, rightExpr); break;
					case ">": guard = Gt(leftExpr, rightExpr); break;
					case "<=": guard = Leq(leftExpr, rightExpr); break;
					case ">=": guard = Geq(leftExpr, rightExpr); break;
				}
				expr = cast(Ite(
						guard,
						Int(1),
						Int(0)
				), Int());
				XcfaMetadata.create(expr, "cType", NamedType.getInt());
			}
			return expr;
		}
		return ctx.shiftExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitShiftExpression(CParser.ShiftExpressionContext ctx) {
		if(ctx.additiveExpression().size() > 1) throw new RuntimeException("Shift expressions should be handled by BitwiseExpressionVisitor");
		else return ctx.additiveExpression().get(0).accept(this);
	}

	@Override
	public Expr<?> visitAdditiveExpression(CParser.AdditiveExpressionContext ctx) {
		if(ctx.multiplicativeExpression().size() > 1) {
			List<NamedType> namedTypes = new ArrayList<>(); // used when deducing the type of the expression
			for(int i = 0; i < ctx.multiplicativeExpression().size(); ++i) {
				Expr<?> expr = ctx.multiplicativeExpression(i).accept(this);
				// get metadata about operand C types
				NamedType cType = CIntTypeUtils.getcTypeMetadata(expr);
				namedTypes.add(cType);
			}
			// use C type metadata to deduce the C type of the additive expression
			NamedType expressionType = CIntTypeUtils.deduceType(namedTypes);

			List<Expr<IntType>> arguments = new ArrayList<>();
			for(int i = 0; i < ctx.multiplicativeExpression().size(); ++i) {
				Expr<?> expr = ctx.multiplicativeExpression(i).accept(this);
				if(i == 0 || ctx.signs.get(i-1).getText().equals("+")) arguments.add(cast(expr, Int()));
				else arguments.add(Neg(cast(expr,Int())));
			}

			IntAddExpr add = Add(arguments);
			XcfaMetadata.create(add, "cType", expressionType);
			Expr<?> expr = CIntTypeUtils.addOverflowWraparound(add);
			return expr;
		}
		return ctx.multiplicativeExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitMultiplicativeExpression(CParser.MultiplicativeExpressionContext ctx) {
		if(ctx.castExpression().size() > 1) {
			List<NamedType> namedTypes = new ArrayList<>(); // used when deducing the type of the expression
			for(int i = 0; i < ctx.castExpression().size(); ++i) {
				Expr<?> expr = ctx.castExpression(i).accept(this);
				NamedType cType = CIntTypeUtils.getcTypeMetadata(expr);
				namedTypes.add(cType);
			}

			// use C type metadata to deduce the C type of the expression
			NamedType expressionType = CIntTypeUtils.deduceType(namedTypes);

			Expr<IntType> expr = null;
			for(int i = 0; i < ctx.castExpression().size() - 1; ++i) {
				Expr<IntType> leftOp, rightOp;
				if(expr == null)
					leftOp = cast(ctx.castExpression(i).accept(this), Int());
				else
					leftOp = expr;
				rightOp = cast(ctx.castExpression(i+1).accept(this), Int());
				switch(ctx.signs.get(i).getText()) {
					case "*":
						// unsigned overflow handling - it "wraps around"
						expr = Mul(leftOp, rightOp);
						XcfaMetadata.create(expr, "cType", expressionType);
						expr = CIntTypeUtils.addOverflowWraparound(expr);
						break;
					case "/":
						expr = Div(leftOp, rightOp);
						XcfaMetadata.create(expr, "cType", expressionType);
						break;
					case "%":
						expr = Rem(leftOp, rightOp);
						XcfaMetadata.create(expr, "cType", expressionType);
						break;
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
		NamedType castType = (NamedType) ctx.typeName().specifierQualifierList().accept(TypeVisitor.instance);
		Expr<IntType> expr = cast(ctx.castExpression().accept(this), Int());
		checkNotNull(castType);
		expr = CIntTypeUtils.explicitCast(castType, expr);
		return expr;
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
			IntAddExpr expr = Add(cast(ret, Int()), Int(increment));
			XcfaMetadata.create(expr, "cType", CIntTypeUtils.getcTypeMetadata(ret));
			Expr<IntType> wrappedExpr = CIntTypeUtils.addOverflowWraparound(expr);
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
				IntNegExpr negExpr = Neg(cast(accept, Int()));
				NamedType type = CIntTypeUtils.getcTypeMetadata(accept);
				XcfaMetadata.create(negExpr, "cType", CIntTypeUtils.deduceType(type));
				return negExpr;
			}
			case "+": return accept; // no need to update type, it remains the same
			case "!":
				IteExpr<?> ite = Ite(Eq(cast(accept, Int()), Int(0)), Int(1), Int(0));
				XcfaMetadata.create(ite, "cType", NamedType.getInt());
				return ite;
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
				IntAddExpr add = Add(cast(primary, Int()), Int(increment));
				XcfaMetadata.create(add, "cType", CIntTypeUtils.getcTypeMetadata(primary));
				CExpr cexpr;
				cexpr = new CExpr(CIntTypeUtils.addOverflowWraparound(add));
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
		NamedType namedType = NamedType("int");
		if(ctx.getText().contains("ll") || ctx.getText().contains("LL")) {
			namedType.setLongLong(true);
		} else if(ctx.getText().contains("l") || ctx.getText().contains("L")) {
			namedType.setLong(true);
		}

		if(ctx.getText().contains("u") || ctx.getText().contains("U") ) {
			namedType.setSigned(false);
		} else namedType.setSigned(true);

		IntLitExpr litExpr = IntLitExpr.of(new BigInteger(ctx.getText().replaceAll("[LUlu]", "")));
		XcfaMetadata.create(litExpr, "cType", namedType);
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
		return Int(-1);
	}


}
