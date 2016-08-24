package hu.bme.mit.inf.theta.core.type;

public interface ArrayType<IndexType extends Type, ElemType extends Type> extends Type {
	
	public IndexType getIndexType();
	public ElemType getElemType();
	
}