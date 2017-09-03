package hu.bme.mit.theta.common.product;

import java.util.List;

public interface Product {

	int arity();

	Object elem(int n);

	public List<? extends Object> toList();

}
