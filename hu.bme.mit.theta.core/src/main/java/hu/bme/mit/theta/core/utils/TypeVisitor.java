package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.type.ArrayType;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.FuncType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.Type;

public interface TypeVisitor<P, R> {

	public R visit(BoolType type, P param);

	public R visit(IntType type, P param);

	public R visit(RatType type, P param);

	public <ParamType extends Type, ResultType extends Type> R visit(FuncType<ParamType, ResultType> type, P param);

	public <IndexType extends Type, ElemType extends Type> R visit(ArrayType<IndexType, ElemType> type, P param);

}
