package hu.bme.mit.inf.ttmc.core.factory;

import hu.bme.mit.inf.ttmc.core.type.ArrayType;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.FuncType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.core.type.Type;

public interface TypeFactory {
	
	public BoolType Bool();

	public IntType Int();

	public RatType Rat();

	public <P extends Type, R extends Type> FuncType<P, R> Func(final P paramTypes, final R resultType);
	
	public <I extends Type, E extends Type> ArrayType<I, E> Array(final I indexType, final E elemType);
	
}
