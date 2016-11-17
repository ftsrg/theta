package hu.bme.mit.theta.common;

import java.util.List;

public interface Product {

	public int arity();

	public Object elem(int n);

	public List<? extends Object> toList();

}
