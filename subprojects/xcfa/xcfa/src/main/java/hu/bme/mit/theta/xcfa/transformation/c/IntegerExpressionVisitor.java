package hu.bme.mit.theta.xcfa.transformation.c;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.xcfa.dsl.gen.CParser;
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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
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
import static hu.bme.mit.theta.xcfa.transformation.c.types.CTypeFactory.NamedType;

public class IntegerExpressionVisitor extends ExpressionVisitor {
	// 32 bit for now, but we'll need to add a 64bit option as well
	// ILP32 Architecture, see here: https://unix.org/whitepapers/64bit.html
	private static final Map<String, Integer> standardTypeSizes = new HashMap<>();

	static {
		standardTypeSizes.put("char", 8);
		standardTypeSizes.put("int", 32);
		standardTypeSizes.put("short", 16);
		standardTypeSizes.put("long", 32);
		standardTypeSizes.put("longlong", 32);
	}

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
			return Ite(
					Neq(Int(0),
							cast(expr, expr.getType())),
					ifTrue.getExpression(),
					ctx.conditionalExpression().accept(this)
					);
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
			return Ite(BoolExprs.Or(collect), Int(1), Int(0));
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
			return Ite(BoolExprs.And(collect), Int(1), Int(0));
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
					leftOp = cast(ctx.relationalExpression(i).accept(this), expr.getType());
				else
					leftOp = expr;
				rightOp = cast(ctx.relationalExpression(i+1).accept(this), expr.getType());
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
		if(ctx.additiveExpression().size() > 1) throw new RuntimeException("Shift expressions should be handled by BitwiseExpressionVisitor");
		else return ctx.additiveExpression().get(0).accept(this);
	}

	@Override
	public Expr<?> visitAdditiveExpression(CParser.AdditiveExpressionContext ctx) {
		if(ctx.multiplicativeExpression().size() > 1) {
			List<NamedType> namedTypes = new ArrayList<>(); // used when deducing the type of the expression
			for(int i = 0; i < ctx.multiplicativeExpression().size(); ++i) {
				Expr<?> expr = ctx.multiplicativeExpression(i).accept(this);
				Optional<Object> cTypeOptional = XcfaMetadata.getMetadataValue(expr,"cType");
				if(cTypeOptional.isPresent() && cTypeOptional.get() instanceof CType) {
					CType cType = (CType) cTypeOptional.get();
					checkState(cType instanceof NamedType);
					namedTypes.add((NamedType) cType);
				}
			}
			CType expressionType = deduceType(namedTypes);
			XcfaMetadata.create(this, "cType", expressionType);

			List<Expr<IntType>> arguments = new ArrayList<>();
			for(int i = 0; i < ctx.multiplicativeExpression().size(); ++i) {
				Expr<?> expr = ctx.multiplicativeExpression(i).accept(this);
				if(i == 0 || ctx.signs.get(i-1).getText().equals("+")) arguments.add(cast(expr, Int()));
				else arguments.add(Neg(cast(expr,Int())));
			}
			// TODO add modulo for overflows
			// return Add(Rem(arguments, CONST));
			return Add(arguments);
		}
		return ctx.multiplicativeExpression(0).accept(this);
	}

	@Override
	public Expr<?> visitMultiplicativeExpression(CParser.MultiplicativeExpressionContext ctx) {
		if(ctx.castExpression().size() > 1) {
			List<NamedType> namedTypes = new ArrayList<>(); // used when deducing the type of the expression
			for(int i = 0; i < ctx.castExpression().size(); ++i) {
				Expr<?> expr = ctx.castExpression(i).accept(this);
				Optional<Object> cTypeOptional = XcfaMetadata.getMetadataValue(expr,"cType");
				if(cTypeOptional.isPresent() && cTypeOptional.get() instanceof CType) {
					CType cType = (CType) cTypeOptional.get();
					checkState(cType instanceof NamedType);
					namedTypes.add((NamedType) cType);
				}
			}
			CType expressionType = deduceType(namedTypes);
			XcfaMetadata.create(this, "cType", expressionType);

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
			CExpr cexpr = new CExpr(Add(cast(ret, Int()), Int(increment)));
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
				CExpr cexpr = new CExpr(Add(cast(primary, Int()), Int(increment)));
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
		return IntLitExpr.of(new BigInteger(ctx.getText().replaceAll("[LUlu]", "")));
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


	/**
	 * Expressions (that are not variables) should have a type based on their operands
	 * Deducing this type follows the logic given below (based on the C11 standard):
	 *
	 * 1. Base types: unsigned/signed char/short/int/long/long long
	 * Note: signed int and int are the same BUT the signedness of char is implementation defined!
	 * (so there are three "chars": unsigned char, signed char and char)
	 * Solution: we shall output a warning if there is a char without explicit signedness, but
	 * by default we will handle it as a signed char.
	 *
	 * 2. Integer promotions
	 * "If an int can represent all values of the original type (as restricted by the width, for a
	 * bit-field), the value is converted to an int; otherwise, it is converted to an unsigned
	 * int. These are called the integer promotions.) All other types are unchanged by the
	 * integer promotions.
	 * The integer promotions preserve value including sign."
	 *
	 * The text above means, that if the types of the operand are a subset of the following:
	 * signed/unsigned short, signed/unsigned char, char, signed int
	 * than the type of the expression shall be signed int
	 * (more precisely, the shorts and chars are "promoted" to signed ints and thus all operands become signed ints,
	 * hence the result type is also a signed int)
	 *
	 * 3. long and long long
	 * If there is a long in the operand types - the expression of the type should also be long
	 * If there is a long long in the operand types - the expression of the type should also be long long
	 *
	 * 4. Signedness
	 * "if the operand that has unsigned integer type has rank greater or
	 * equal to the rank of the type of the other operand, then the operand with
	 * signed integer type is converted to the type of the operand with unsigned
	 * integer type."
	 *
	 * so if in the "highest ranked" types (int<long<longlong) there is an unsigned one, than the expression type
	 * shall also be unsigned. Otherwise it shall be signed
	 *
	 * 5. volatility and other attributes
	 * - an expression is volatile if there is at least one volatile variable in it
	 * - an expression cannot be atomic or extern
	 *
	 * @param namedTypes list of the types of the operands in the expression
	 * @return the deduced type of the expression
	 */
	// TODO what should we do when void?
	// TODO handle empty list
	private CType deduceType(List<NamedType> namedTypes) {
		boolean signed = true;
		boolean isVolatile = false;
		boolean containsLong = false;
		boolean containsLongLong = false;

		for (NamedType type : namedTypes) {
			// non-supported:
			checkState(type.getPointerLevel()==0);

			// just to make sure, that we don't get any unsupported types here
			if(!(type.getNamedType().contains("int") || type.getNamedType().contains("char"))) {
				throw new RuntimeException("Typed should contains int or char, instead it is: " + type.getNamedType());
			}

			if(type.isVolatile()) { // if there is any volatile type, the deduced type should be volatile as well
				isVolatile = true;
			}

			if(type.isLong()) {
				containsLong = true;
			} else if(type.isLongLong()) {
				containsLongLong = true;
			}

		}

		if(containsLongLong) {
			if (namedTypes.stream().anyMatch(type -> type.getNamedType().contains("int") && type.isLongLong() && !type.isSigned())) {
				signed = false;
			}
		}
		else if(containsLong) {
			if(namedTypes.stream().anyMatch(type -> type.getNamedType().contains("int") && type.isLong() && !type.isSigned())) {
				signed = false;
			}
		} else {
			if(namedTypes.stream().anyMatch(type -> type.getNamedType().contains("int") && !type.isShort() && !type.isSigned())) {
				signed = false;
			}
		}

		NamedType deducedType = NamedType("int");
		deducedType.setAtomic(false); // only vars can be atomic or extern
		deducedType.setExtern(false);
		deducedType.setShort(false);
		deducedType.setSigned(signed);
		deducedType.setVolatile(isVolatile);
		deducedType.setLong(containsLong);
		deducedType.setLongLong(containsLongLong);
		return deducedType;
	}

}
