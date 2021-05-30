package hu.bme.mit.theta.xcfa.transformation.c.declaration;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CStatement;
import hu.bme.mit.theta.xcfa.transformation.c.types.CType;

import java.util.ArrayList;
import java.util.List;

public class CDeclaration {
	private CType baseType;
	private final String name;
	private boolean isFunc;
	private int derefCounter = 0;
	private final List<CStatement> arrayDimensions = new ArrayList<>();
	private final List<CDeclaration> functionParams = new ArrayList<>();
	private CStatement initExpr;

	public CDeclaration(CType cType) {
		this.name = null;
		this.baseType = cType.getBaseType();
		this.derefCounter = cType.getPointerLevel();
	}
	public CDeclaration(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	public int getDerefCounter() {
		return derefCounter;
	}

	public void incDerefCounter(int amount) {
		derefCounter+=amount;
	}

	public void addArrayDimension(CStatement expr) {
		arrayDimensions.add(expr);
	}

	public List<CStatement> getArrayDimensions() {
		return arrayDimensions;
	}

	public void addFunctionParam(CDeclaration decl) {
		functionParams.add(decl);
	}

	public List<CDeclaration> getFunctionParams() {
		return functionParams;
	}

	public CType getBaseType() {
		return baseType;
	}

	public void setBaseType(CType baseType) {
		this.baseType = baseType;
	}

	public CStatement getInitExpr() {
		return initExpr;
	}

	public void setInitExpr(CStatement initExpr) {
		this.initExpr = initExpr;
	}

	@Override
	public String toString() {
		StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append(baseType).append(" ");
		stringBuilder.append("*".repeat(Math.max(0, derefCounter)));
		stringBuilder.append(name == null ? "" : name);
		for (CStatement arrayDimension : arrayDimensions) {
			stringBuilder.append("[]");
		}
		if(isFunc) stringBuilder.append("(");
		for (CDeclaration functionParam : functionParams) {
			stringBuilder.append(functionParam).append(", ");
		}
		if(isFunc) stringBuilder.append(")");
		if(initExpr != null) {
			stringBuilder.append(" = ").append(initExpr);
		}
		return stringBuilder.toString();
	}

	public boolean isFunc() {
		return isFunc;
	}

	public void setFunc(boolean func) {
		isFunc = func;
	}
}
