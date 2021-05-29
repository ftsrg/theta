package hu.bme.mit.theta.xcfa.transformation.c.types;

import hu.bme.mit.theta.core.type.Expr;

import java.util.Map;
import java.util.Optional;

public class Enum extends CType{
	private final String id;
	private final Map<String, Optional<Expr<?>>> fields;
	Enum(String id, Map<String, Optional<Expr<?>>> fields){
		this.fields = fields;
		this.id = id;
	}

	public Map<String, Optional<Expr<?>>> getFields() {
		return fields;
	}

	public String getId() {
		return id;
	}

	@Override
	protected void patch(CType cType) {

	}
}
