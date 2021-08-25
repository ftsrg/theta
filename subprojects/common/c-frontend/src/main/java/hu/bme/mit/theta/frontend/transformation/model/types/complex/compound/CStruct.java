package hu.bme.mit.theta.frontend.transformation.model.types.complex.compound;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

import java.util.Map;

public class CStruct extends CCompound {
	private final Map<String, CComplexType> fields;
	public CStruct(CSimpleType origin, Map<String, CComplexType> fields) {
		super(origin);
		this.fields = fields;
	}

	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}

	public Map<String, CComplexType> getFields() {
		return fields;
	}
}
