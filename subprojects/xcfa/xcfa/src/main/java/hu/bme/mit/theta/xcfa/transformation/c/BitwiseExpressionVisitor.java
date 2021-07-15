package hu.bme.mit.theta.xcfa.transformation.c;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvAddExpr;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvMulExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNegExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSDivExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSGeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSGtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSLeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSLtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSRemExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.bvtype.BvUDivExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUGeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUGtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvULeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvULtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvURemExpr;
import hu.bme.mit.theta.core.type.inttype.IntAddExpr;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.xcfa.CBvTypeUtils;
import hu.bme.mit.theta.xcfa.CIntTypeUtils;
import hu.bme.mit.theta.xcfa.dsl.gen.CParser;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.transformation.c.declaration.CDeclaration;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CAssignment;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CStatement;
import hu.bme.mit.theta.xcfa.transformation.c.types.NamedType;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

// TODO
public class BitwiseExpressionVisitor extends ExpressionVisitor {

	public BitwiseExpressionVisitor(Deque<Map<String, VarDecl<?>>> variables, Map<VarDecl<?>, CDeclaration> functions) {
		super(variables, functions);
	}

	// TODO line TODO

	@Override
	public Expr<?> visitConditionalExpression(CParser.ConditionalExpressionContext ctx) {
		if(ctx.expression() != null) {
			CStatement ifTrue = ctx.expression().accept(FunctionVisitor.instance);
			if(ifTrue instanceof CAssignment) {
				preStatements.add(ifTrue);
			}
			Expr<?> expr = ctx.logicalOrExpression().accept(this);
			NamedType cType = CBvTypeUtils.getcTypeMetadata(expr);
			IteExpr<?> ite = Ite(
					Neq(CBvTypeUtils.getBvValueOfType(cType, 0),
							cast(expr, expr.getType())),
					ifTrue.getExpression(),
					ctx.conditionalExpression().accept(this)
			);
			XcfaMetadata.create(ite, "cType", cType);
			return ite;
		}
		else return ctx.logicalOrExpression().accept(this);
	}

	@Override
	public Expr<?> visitLogicalOrExpression(CParser.LogicalOrExpressionContext ctx) {
		if(ctx.logicalAndExpression().size() > 1) {
			List<NeqExpr<?>> collect = ctx.logicalAndExpression().stream().map(logicalAndExpressionContext -> {
				Expr<?> expr = logicalAndExpressionContext.accept(this);
				return Neq(CBvTypeUtils.getBvValueOfType(CBvTypeUtils.getcTypeMetadata(expr), 0), cast(expr, expr.getType())); }).
					collect(Collectors.toList());
			IteExpr<?> ite = Ite(BoolExprs.Or(collect), BvUtils.bigIntegerToUnsignedBvLitExpr(BigInteger.valueOf(1), 1),
														BvUtils.bigIntegerToUnsignedBvLitExpr (BigInteger.valueOf(0),1)
								);
			XcfaMetadata.create(ite, "cType", NamedType.getBoolType());
			return ite;
		}
		return ctx.logicalAndExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitLogicalAndExpression(CParser.LogicalAndExpressionContext ctx) {
		if(ctx.inclusiveOrExpression().size() > 1) {
			List<Expr<BoolType>> collect = ctx.inclusiveOrExpression().stream().map(inclusiveOrExpressionContext -> {
				Expr<?> expr = inclusiveOrExpressionContext.accept(this);
				return Neq(CBvTypeUtils.getBvValueOfType(CBvTypeUtils.getcTypeMetadata(expr), 0), cast(expr, expr.getType())); }).
					collect(Collectors.toList());
			IteExpr<?> ite = Ite(BoolExprs.And(collect), BvUtils.bigIntegerToUnsignedBvLitExpr(BigInteger.valueOf(1), 1),
					BvUtils.bigIntegerToUnsignedBvLitExpr (BigInteger.valueOf(0),1)
			);
			XcfaMetadata.create(ite, "cType", NamedType.getBoolType());
			return ite;
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
			Expr<BvType> expr = null;
			for(int i = 0; i < ctx.relationalExpression().size() - 1; ++i) {
				Expr<BvType> leftOp, rightOp;
				if(expr == null) {
					Expr<?> accept = ctx.relationalExpression(i).accept(this);
					NamedType cType = CBvTypeUtils.getcTypeMetadata(accept);
					leftOp = cast(accept, BvType.of(CBvTypeUtils.getBitWidth(cType)));
				}
				else
					leftOp = expr;
				Expr<?> rightAccept = ctx.relationalExpression(i + 1).accept(this);
				NamedType rightCType = CBvTypeUtils.getcTypeMetadata(rightAccept);
				rightOp = cast(rightAccept, BvType.of(CBvTypeUtils.getBitWidth(rightCType)));

				Tuple2<Expr<BvType>, Expr<BvType>> exprTuple2 = CBvTypeUtils.castToCommonType(leftOp, rightOp);
				Expr<BvType> leftExpr = exprTuple2.get1();
				Expr<BvType> rightExpr = exprTuple2.get2();
				expr = cast(Ite(
						ctx.signs.get(i).getText().equals("==") ? Eq(leftExpr, rightExpr) : Neq(leftOp, rightOp),
						BvUtils.bigIntegerToUnsignedBvLitExpr(BigInteger.valueOf(1), 1),
						BvUtils.bigIntegerToUnsignedBvLitExpr (BigInteger.valueOf(0),1)
				), BvType.of(1));
				XcfaMetadata.create(expr, "cType", NamedType.getBoolType());
			}
			return expr;
		}
		return ctx.relationalExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitRelationalExpression(CParser.RelationalExpressionContext ctx) {
		if(ctx.shiftExpression().size() > 1) {
			Expr<BvType> expr = null;
			for(int i = 0; i < ctx.shiftExpression().size() - 1; ++i) {
				Expr<BvType> leftOp, rightOp;
				if(expr == null) {
					Expr<?> accept = ctx.shiftExpression(i).accept(this);
					NamedType cType = CBvTypeUtils.getcTypeMetadata(accept);
					leftOp = cast(accept, BvType.of(CBvTypeUtils.getBitWidth(cType)));
				}
				else
					leftOp = expr;
				Expr<?> rightAccept = ctx.shiftExpression(i + 1).accept(this);
				NamedType rightCType = CBvTypeUtils.getcTypeMetadata(rightAccept);
				rightOp = cast(rightAccept, BvType.of(CBvTypeUtils.getBitWidth(rightCType)));

				Expr<BoolType> guard = null;
				Tuple2<Expr<BvType>, Expr<BvType>> exprTuple2 = CBvTypeUtils.castToCommonType(leftOp, rightOp);
				Expr<BvType> leftExpr = exprTuple2.get1();
				Expr<BvType> rightExpr = exprTuple2.get2();

				if(CBvTypeUtils.getcTypeMetadata(leftExpr).isSigned()) {
					switch(ctx.signs.get(i).getText()) {
						case "<": guard = BvSLtExpr.of(leftExpr, rightExpr); break;
						case ">": guard = BvSGtExpr.of(leftExpr, rightExpr); break;
						case "<=": guard = BvSLeqExpr.of(leftExpr, rightExpr); break;
						case ">=": guard = BvSGeqExpr.of(leftExpr, rightExpr); break;
					}

				} else {
					switch(ctx.signs.get(i).getText()) {
						case "<": guard = BvULtExpr.of(leftExpr, rightExpr); break;
						case ">": guard = BvUGtExpr.of(leftExpr, rightExpr); break;
						case "<=": guard = BvULeqExpr.of(leftExpr, rightExpr); break;
						case ">=": guard = BvUGeqExpr.of(leftExpr, rightExpr); break;
					}
				}

				expr = cast(Ite(
						guard,
						BvUtils.bigIntegerToUnsignedBvLitExpr(BigInteger.valueOf(1), 1),
						BvUtils.bigIntegerToUnsignedBvLitExpr (BigInteger.valueOf(0),1)
				), BvType.of(1));

				XcfaMetadata.create(expr, "cType", NamedType.getBoolType());
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
			List<NamedType> namedTypes = new ArrayList<>(); // used when deducing the type of the expression
			for(int i = 0; i < ctx.multiplicativeExpression().size(); ++i) {
				Expr<?> expr = ctx.multiplicativeExpression(i).accept(this);
				// get metadata about operand C types
				NamedType cType = CBvTypeUtils.getcTypeMetadata(expr);
				namedTypes.add(cType);
			}
			// use C type metadata to deduce the C type of the additive expression
			NamedType expressionType = CBvTypeUtils.deduceType(namedTypes);

			List<Expr<BvType>> arguments = new ArrayList<>();
			for(int i = 0; i < ctx.multiplicativeExpression().size(); ++i) {
				Expr<?> expr = ctx.multiplicativeExpression(i).accept(this);
				if(i == 0 || ctx.signs.get(i-1).getText().equals("+")) arguments.add(cast(expr, BvType.of(CBvTypeUtils.getBitWidth(expressionType))));
				else arguments.add(BvNegExpr.of(cast(expr,BvType.of(CBvTypeUtils.getBitWidth(expressionType)))));
			}

			BvAddExpr add = BvAddExpr.of(arguments);
			XcfaMetadata.create(add, "cType", expressionType);
			Expr<?> expr = CBvTypeUtils.addOverflowWraparound(add);
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
				NamedType cType = CBvTypeUtils.getcTypeMetadata(expr);
				namedTypes.add(cType);
			}

			// use C type metadata to deduce the C type of the expression
			NamedType expressionType = CBvTypeUtils.deduceType(namedTypes);

			Expr<BvType> expr = null;
			for(int i = 0; i < ctx.castExpression().size() - 1; ++i) {
				Expr<BvType> leftOp, rightOp;

				if(expr == null) {
					Expr<?> accept = ctx.castExpression(i).accept(this);
					NamedType cType = CBvTypeUtils.getcTypeMetadata(accept);
					leftOp = CBvTypeUtils.explicitCast(expressionType, cast(accept, BvType.of(CBvTypeUtils.getBitWidth(cType))));
				}
				else
					leftOp = expr;

				Expr<?> rightAccept = ctx.castExpression(i + 1).accept(this);
				NamedType rightCType = CBvTypeUtils.getcTypeMetadata(rightAccept);
				rightOp = CBvTypeUtils.explicitCast(expressionType, cast(rightAccept, BvType.of(CBvTypeUtils.getBitWidth(rightCType))));

				switch(ctx.signs.get(i).getText()) {
					case "*":
						// unsigned overflow handling - it "wraps around"
						expr = BvMulExpr.of(List.of(leftOp, rightOp));
						XcfaMetadata.create(expr, "cType", expressionType);
						expr = CBvTypeUtils.addOverflowWraparound(expr);
						break;
					case "/":
						if(CBvTypeUtils.getcTypeMetadata(leftOp).isSigned()) {
							expr = BvSDivExpr.of(leftOp, rightOp);
							XcfaMetadata.create(expr, "cType", expressionType);
						} else {
							expr = BvUDivExpr.of(leftOp, rightOp);
							XcfaMetadata.create(expr, "cType", expressionType);
						}
						break;
					case "%":
						if(CBvTypeUtils.getcTypeMetadata(leftOp).isSigned()) {
							expr = BvSRemExpr.of(leftOp, rightOp);
							XcfaMetadata.create(expr, "cType", expressionType);
						} else {
							expr = BvURemExpr.of(leftOp, rightOp);
							XcfaMetadata.create(expr, "cType", expressionType);
						}
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
