package hu.bme.mit.inf.ttmc.constraint.type;


import java.util.List;


public interface TupleType extends Type {
	public List<? extends Type> getElemTypes();
	
}
