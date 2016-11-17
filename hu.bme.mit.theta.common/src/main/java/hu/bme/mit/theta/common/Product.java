package hu.bme.mit.theta.common;

import java.util.List;

public interface Product extends Iterable<Object> {

	public int arity();

	public Object elem(int n);

	public List<Object> toList();

}
