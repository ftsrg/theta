package hu.bme.mit.theta.frontend.transformation.model.types.simple;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct;

import java.util.LinkedHashMap;
import java.util.Map;

public class Struct extends NamedType {
	private final Map<String, CSimpleType> fields;
	private final String name;
	private boolean currentlyBeingBuilt;
	private static final Map<String, Struct> definedTypes = new LinkedHashMap<>();

	public static Struct getByName(String name) {
		return definedTypes.get(name);
	}

	Struct(String name){
		super("struct");
		fields = new LinkedHashMap<>();
		this.name = name;
		if(name != null) definedTypes.put(name, this);
		currentlyBeingBuilt = false;
	}

	public void addField(String name, CSimpleType type) {
		fields.put(name, type);
	}

	@Override
	public CComplexType getActualType() {
		if(currentlyBeingBuilt) {
			System.err.println("WARNING: self-embedded structs! Using long as a placeholder");
			return CComplexType.getSignedInt();
		}
		currentlyBeingBuilt = true;
		Map<String, CComplexType> actualFields = new LinkedHashMap<>();
		fields.forEach((s, cSimpleType) -> actualFields.put(s, cSimpleType.getActualType()));
		currentlyBeingBuilt = false;
		return new CStruct(this, actualFields);
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

