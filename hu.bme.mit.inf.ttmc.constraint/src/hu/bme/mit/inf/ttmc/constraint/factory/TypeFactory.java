package hu.bme.mit.inf.ttmc.constraint.factory;

import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface TypeFactory {
	
	public BoolType Bool();

	public IntType Int();

	public RatType Rat();

	public <P extends Type, R extends Type> FuncType<P, R> Func(final P paramTypes, final R resultType);
	
	public <I extends Type, E extends Type> ArrayType<I, E> Array(final I indexType, final E elemType);
	
}
