package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntType;

import java.math.BigInteger;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class XstsTypeLiteralSymbol implements Symbol {

	private final BigInteger intValue;
	private final String name;

	private static int counter = 0;

	public XstsTypeLiteralSymbol(String name) {
		this.intValue = BigInteger.valueOf(counter++);
		this.name = checkNotNull(name);
	}

	@Override
	public String getName() {
		return name;
	}

	public BigInteger getIntValue(){
		return intValue;
	}

	public Expr<IntType> instantiate(){
		return Int(intValue);
	}

	@Override
	public String toString() {
		return name + "=" + intValue;
	}
}
