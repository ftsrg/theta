package hu.bme.mit.theta.xcfa.transformation.model.types.simple;

import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.compound.CStruct;

import java.util.LinkedHashMap;
import java.util.Map;

public class Struct extends NamedType {
	private final Map<String, CSimpleType> fields;
	private final String name;
	private static final Map<String, Struct> definedTypes = new LinkedHashMap<>();

	public static Struct getByName(String name) {
		return definedTypes.get(name);
	}

	Struct(String name){
		super("struct");
		fields = new LinkedHashMap<>();
		this.name = name;
		if(name != null) definedTypes.put(name, this);
	}

	public void addField(String name, CSimpleType type) {
		fields.put(name, type);
	}

	@Override
	public CComplexType getActualType() {
		Map<String, CComplexType> actualFields = new LinkedHashMap<>();
		fields.forEach((s, cSimpleType) -> actualFields.put(s, cSimpleType.getActualType()));
		return new CStruct(this, actualFields);
	}

	@Override
	protected void patch(CSimpleType cSimpleType) {
		throw new UnsupportedOperationException("Not patchable!");
	}

	@Override
	public CSimpleType getBaseType() {
		return this;
	}

	@Override
	public boolean isVoid() {
		return false;
	}

	@Override
	public CSimpleType copyOf() {
		Struct struct = new Struct(name);
		struct.fields.putAll(fields);
		return struct;
	}
}

