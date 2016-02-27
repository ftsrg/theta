package hu.bme.mit.inf.ttmc.constraint.type;

public interface ArrayType<IndexType extends Type, ElemType extends Type> extends Type {
	
	public IndexType getIndexType();
	public ElemType getElemType();
	
}