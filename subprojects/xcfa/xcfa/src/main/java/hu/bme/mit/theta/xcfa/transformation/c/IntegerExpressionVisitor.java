package hu.bme.mit.theta.xcfa.transformation.c;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.inttype.IntAddExpr;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntRemExpr;
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

import javax.naming.Name;
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
	// TODO 32 bit for now, but we'll need to add a 64bit option as well
	// ILP32 Architecture, see here: https://unix.org/whitepapers/64bit.html
	// Warning note: when deducing type, we assume an ILP32 or an LP64 arch
	// (e.g. conversion rules would get more complex, if an int isn't at least twice as big as a short)
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
			NamedType expressionType = deduceType(namedTypes);
			XcfaMetadata.create(this, "cType", expressionType);

			List<Expr<IntType>> arguments = new ArrayList<>();
			for(int i = 0; i < ctx.multiplicativeExpression().size(); ++i) {
				Expr<?> expr = ctx.multiplicativeExpression(i).accept(this);
				if(i == 0 || ctx.signs.get(i-1).getText().equals("+")) arguments.add(cast(expr, Int()));
				else arguments.add(Neg(cast(expr,Int())));
			}

			// unsigned overflow/underflow
			if(!expressionType.isSigned()) {
				int maxBits = standardTypeSizes.get(expressionType.getNamedType());
				return Rem(Add(arguments), Int((int) Math.pow(2, maxBits)));
			}
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
	 * Solution: we output a warning (not in this function) if there is a char without explicit signedness, but
	 * by default we will handle it as a signed char.
	 *
	 * 2. Integer promotions
	 * "If an int can represent all values of the original type (as restricted by the width, for a
	 * bit-field), the value is converted to an int; otherwise, it is converted to an unsigned
	 * int. These are called the integer promotions.) All other types are unchanged by the
	 * integer promotions.
	 * The integer promotions preserve value including sign."
	 *
	 * 3. Usual arithmetic conversions
	 * "the integer promotions are performed on both operands. Then the
	 * following rules are applied to the promoted operands:
	 * 	If both operands have the same type, then no further conversion is needed.
	 * Otherwise, if both operands have signed integer types or both have unsigned
	 * integer types, the operand with the type of lesser integer conversion rank is
	 * converted to the type of the operand with greater rank.
	 *
	 * 	Otherwise, if the operand that has unsigned integer type has rank greater or
	 * equal to the rank of the type of the other operand, then the operand with
	 * signed integer type is converted to the type of the operand with unsigned
	 * integer type.
	 *
	 * 	Otherwise, if the type of the operand with signed integer type can represent
	 * all of the values of the type of the operand with unsigned integer type, then
	 * the operand with unsigned integer type is converted to the type of the
	 * operand with signed integer type.
	 *
	 * 	Otherwise, both operands are converted to the unsigned integer type
	 * corresponding to the type of the operand with signed integer type."
	 *
	 * 4. volatility and other attributes
	 * - an expression is volatile if there is at least one volatile variable in it
	 * - an expression cannot be atomic or extern
	 *
	 * Warning note: when deducing type, we assume an ILP32 or an LP64 arch
	 * (e.g. conversion rules would get more complex, if an int isn't at least twice as big as a short)
	 *
	 * @param namedTypes list of the types of the operands in the expression
	 * @return the deduced type of the expression
	 */
	// TODO what should we do when void?
	private NamedType deduceType(List<NamedType> namedTypes) {
		checkState(!namedTypes.isEmpty());
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

	/**
	 * The usual arithmetic conversions and other implicit conversion rules of the C standard are
	 * given for two operands, so the straightforward way of implementation is pairwise deduction.
	 * conversion rules: {@link #deduceType(List)}  }
	 *
	 * @param typeA First operand type
	 * @param typeB Second operand type
	 * @return the resulting type, which is not necessarily typeA or typeB
	 */
	private NamedType deduceTypeBinary(NamedType typeA, NamedType typeB) {
		NamedType resultType = NamedType("int");
		if(typeA.isVolatile() || typeB.isVolatile()) {
			resultType.setVolatile(true);
		}
		resultType.setAtomic(false);
		resultType.setExtern(false);

		// integer promotion
		NamedType typeACopy = promoteToInteger(typeA);
		NamedType typeBCopy = promoteToInteger(typeB);

		// usual arithmetic conversions
		// same types
		if(typeACopy.isLongLong() == typeBCopy.isLongLong() &&
			typeACopy.isLong() == typeBCopy.isLong() &&
			typeACopy.isSigned() == typeBCopy.isSigned()) {
			copyIntType(typeACopy, resultType);
		}
		// both signed or both unsigned -> rank
		else if(typeACopy.isSigned() == typeBCopy.isSigned()) {
			if(rankLessThan(typeACopy, typeBCopy)) {
				copyIntType(typeBCopy, resultType);
			} else copyIntType(typeACopy, resultType);
		} else {
			NamedType unsignedType = typeA.isSigned() ? typeBCopy : typeACopy;
			NamedType signedType = typeA.isSigned() ? typeACopy : typeBCopy;

			// unsigned has >= rank -> unsigned type
			if(rankLessThan(signedType, unsignedType)) {
				copyIntType(unsignedType, resultType);
			} else if(standardTypeSizes.get(signedType.getNamedType()) >= 2*standardTypeSizes.get(unsignedType.getNamedType())) {
			// unsigned has < rank & signed is at least twice the size -> signed type
				copyIntType(signedType, resultType);
			} else {
			// unsigned has < rank & signed is less than twice the size -> unsigned version of signed type
				copyIntType(signedType, resultType);
				resultType.setSigned(false);
			}
		}
		return resultType;
	}

	/**
	 * Copies the short, long, longlong and signedness attributes and nothing else
	 *
	 * @param src copy to
	 * @param dest copy from
	 */
	private void copyIntType(NamedType src, NamedType dest) {
		dest.setShort(src.isShort());
		dest.setLong(src.isLong());
		dest.setLongLong(src.isLongLong());
		dest.setSigned(src.isSigned());
	}

	private boolean rankLessThan(NamedType typeA, NamedType typeB) {
		if(typeA.getNamedType().contains("char")) {
			if(typeB.getNamedType().contains("char")) { // both are chars
				return false;
			} else return true; // only A is a char
		} else if(typeB.getNamedType().contains("char")) { // only B is a char
			return true;
		} else { // both are ints
			if (typeB.isLongLong() && !typeA.isLongLong()) {
				return true;
			} else if (typeB.isLong() && !typeA.isLongLong() && !typeA.isLong()) {
				return true;
			} else if (!typeB.isShort() && typeA.isShort()) {
				return true;
			} else return false;
		}
	}

	/**
	 * Integer promotions
	 * 	 "If an int can represent all values of the original type (as restricted by the width, for a
	 * 	 bit-field), the value is converted to an int; otherwise, it is converted to an unsigned
	 * 	 int. These are called the integer promotions.) All other types are unchanged by the
	 * 	 integer promotions.
	 * 	 The integer promotions preserve value including sign."
	 *
	 * Assumption: we are in an architecture, where a signed integer can represent all values of both
	 * signed and unsigned shorts or chars (ILP32 and LP64 are such)
	 *
	 * @param type type to promote
	 * @return promoted type, it must be an int and cannot be short
	 */
	private NamedType promoteToInteger(NamedType type) {
		// integer promotion
		NamedType typeCopy = null;
		if(type.getNamedType().contains("char")) {
			typeCopy = NamedType("int");
			typeCopy.setSigned(true);
			typeCopy.setLongLong(false);
			typeCopy.setLong(false);
		} else if(type.isShort()) {
			typeCopy = (NamedType) type.copyOf();
			typeCopy.setShort(false);
			typeCopy.setSigned(true);
		} else {
			typeCopy = (NamedType) type.copyOf();
		}
		return typeCopy;
	}
}
