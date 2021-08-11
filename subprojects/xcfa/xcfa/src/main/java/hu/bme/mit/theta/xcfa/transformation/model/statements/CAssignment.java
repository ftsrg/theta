package hu.bme.mit.theta.xcfa.transformation.model.statements;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.transformation.grammar.expression.Dereference;
import hu.bme.mit.theta.xcfa.transformation.grammar.expression.Reference;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.compound.CPointer;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Write;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class CAssignment extends CStatement{
	private final Expr<?> lValue;
	private final CStatement rValue;
	private final String operator;
	private static final Map<Type, VarDecl<ArrayType<?, ?>>> memoryMaps = new LinkedHashMap<>();

	public CAssignment(Expr<?> lValue, CStatement rValue, String operator) {
		checkNotNull(rValue.getExpression());
		this.lValue = lValue;
		this.rValue = rValue;
		this.operator = operator;
	}

	public CStatement getrValue() {
		return rValue;
	}

	public Expr<?> getlValue() {
		return lValue;
	}

	@Override
	public Expr<?> getExpression() {
		return lValue;
	}

	public Expr<?> getrExpression() {
		Expr<?> ret = null;
		switch (operator) {
			case "=": return rValue.getExpression();
			case "*=": ret = AbstractExprs.Mul(lValue, rValue.getExpression()); break;
			case "/=": ret = AbstractExprs.Div(lValue, rValue.getExpression()); break;
			case "%=": ret = AbstractExprs.Mod(lValue, rValue.getExpression()); break;
			case "+=": ret = AbstractExprs.Add(lValue, rValue.getExpression()); break;
			case "-=": ret = AbstractExprs.Sub(lValue, rValue.getExpression()); break;
			default: throw new RuntimeException("Bad operator!");
		}
		XcfaMetadata.create(ret, "cType", CComplexType.getType(lValue));
		ret = CComplexType.getType(lValue).castTo(ret);
		XcfaMetadata.create(ret, "cType", CComplexType.getType(lValue));
		return ret;
	}

	@Override
	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		XcfaLocation initLoc = getLoc() == null ? new XcfaLocation("loc" + counter++, Map.of()) : getLoc();
		builder.addLoc(initLoc);
		propagateMetadata(initLoc);
		XcfaEdge xcfaEdge = new XcfaEdge(lastLoc, initLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(xcfaEdge);
		XcfaLocation location = new XcfaLocation("loc" + counter++, Map.of());
		builder.addLoc(location);
		propagateMetadata(location);
		initLoc = rValue.build(builder, initLoc, breakLoc, continueLoc, returnLoc);
		checkState(lValue instanceof Dereference || lValue instanceof ArrayReadExpr || lValue instanceof RefExpr && ((RefExpr<?>) lValue).getDecl() instanceof VarDecl<?>, "lValue must be a variable, pointer dereference or an array element!");
		Expr<?> rExpression = getrExpression();
		if (lValue instanceof ArrayReadExpr) {
			Stack<Expr<?>> exprs = new Stack<>();
			Expr<?> expr = rExpression;
			VarDecl<?> var = createArrayWriteExpr((ArrayReadExpr<?, ? extends Type>) lValue, expr, exprs);
			xcfaEdge = new XcfaEdge(initLoc, location, List.of(Assign(cast(var, var.getType()), cast(exprs.pop(), var.getType()))));
			builder.addEdge(xcfaEdge);
			propagateMetadata(xcfaEdge);
		} else if (lValue instanceof Dereference) {
			Expr<?> op = ((Dereference<?, ?>) lValue).getOp();
			Type type = op.getType();
			Type ptrType = CComplexType.getUnsignedLong().getSmtType();
			if(!memoryMaps.containsKey(type)) {
				memoryMaps.put(type, Var("memory_" + type.toString(),  ArrayType.of(ptrType, type)));
			}
			VarDecl<ArrayType<?, ?>> memoryMap = memoryMaps.get(type);
			XcfaMetadata.create(op, "dereferenced", true);
			XcfaMetadata.create(op, "refSubstitute", memoryMap);
			Expr<?> expr = rExpression;
			ArrayWriteExpr<Type, Type> write = Write(cast(memoryMap.getRef(), ArrayType.of(ptrType, type)),
					cast(((Dereference<?, ?>) lValue).getOp(), ptrType),
					cast(expr, type));
			XcfaMetadata.create(write, "cType", new CArray(null, CComplexType.getType(((Dereference<?, ?>) lValue).getOp())));
			xcfaEdge = new XcfaEdge(initLoc, location, List.of(Assign(cast(memoryMap, ArrayType.of(ptrType, type)), write)));
			builder.addEdge(xcfaEdge);
			propagateMetadata(xcfaEdge);
		}
		else {
			xcfaEdge = new XcfaEdge(initLoc, location, List.of(Assign(cast((VarDecl<?>) ((RefExpr<?>) lValue).getDecl(), ((VarDecl<?>) ((RefExpr<?>) lValue).getDecl()).getType()), cast(rExpression, rExpression.getType()))));
			if(CComplexType.getType(lValue) instanceof CPointer && CComplexType.getType(rExpression) instanceof CPointer) {
				checkState(rExpression instanceof RefExpr || rExpression instanceof Reference);
				if(rExpression instanceof RefExpr) XcfaMetadata.create(lValue, "pointsTo", rExpression);
				else XcfaMetadata.create(lValue, "pointsTo", ((Reference<?, ?>) rExpression).getOp());
			}
			builder.addEdge(xcfaEdge);
			propagateMetadata(xcfaEdge);
		}
		return location;
	}


	private <P extends Type, T extends Type> VarDecl<?> createArrayWriteExpr(ArrayReadExpr<P, T> lValue, Expr<?> rExpression, Stack<Expr<?>> exprs) {
		Expr<ArrayType<P, T>> array = lValue.getArray();
		Expr<P> index = lValue.getIndex();
		ArrayWriteExpr<P, T> arrayWriteExpr = ArrayWriteExpr.of(array, index, cast(rExpression, array.getType().getElemType()));
		XcfaMetadata.create(arrayWriteExpr, "cType", new CArray(null, CComplexType.getType(rExpression)));
		if (array instanceof RefExpr && ((RefExpr<ArrayType<P, T>>) array).getDecl() instanceof VarDecl) {
			exprs.push(arrayWriteExpr);
			return (VarDecl<?>) ((RefExpr<ArrayType<P, T>>) array).getDecl();
		} else if (array instanceof ArrayReadExpr) {
			return createArrayWriteExpr((ArrayReadExpr<P, ?>) array, arrayWriteExpr, exprs);
		} else throw new UnsupportedOperationException("Possible malformed array write?");
	}
}
