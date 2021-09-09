package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xsts.type.XstsCustomType;

import java.math.BigInteger;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class XstsCustomLiteralSymbol implements Symbol {

	private final XstsCustomType.XstsCustomLiteral literal;

	private static int counter = 0;

	public XstsCustomLiteralSymbol(String name) {
		this.literal = XstsCustomType.XstsCustomLiteral.of(name, BigInteger.valueOf(counter++));
	}

	@Override
	public String getName() {
		return literal.getName();
	}

	@Override
	public String toString() {
		return literal.toString();
	}

	public Expr instantiate(){
		return Int(literal.getIntValue());
	}

	public XstsCustomType.XstsCustomLiteral getLiteral() {
		return literal;
	}
}
