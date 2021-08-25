package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;

import java.util.LinkedHashMap;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

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

	public String getOperator() {
		return operator;
	}

	public static Map<Type, VarDecl<ArrayType<?, ?>>> getMemoryMaps() {
		return memoryMaps;
	}

	@Override
	public Expr<?> getExpression() {
		return lValue;
	}

	@Override
	public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
		return visitor.visit(this, param);
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
		FrontendMetadata.create(ret, "cType", CComplexType.getType(lValue));
		ret = CComplexType.getType(lValue).castTo(ret);
		FrontendMetadata.create(ret, "cType", CComplexType.getType(lValue));
		return ret;
	}
}
