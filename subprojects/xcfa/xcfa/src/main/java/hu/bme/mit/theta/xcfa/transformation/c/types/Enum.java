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
		throw new RuntimeException("Should not be here! Cannot patch with an enum.");
	}

	@Override
	public CType getBaseType() {
		Enum anEnum = new Enum(id, fields);
		anEnum.setAtomic(this.isAtomic());
		anEnum.setExtern(this.isExtern());
		anEnum.setTypedef(this.isTypedef());
		anEnum.setVolatile(this.isVolatile());
		return anEnum;
	}
}
