package hu.bme.mit.theta.xcfa;

import java.util.HashMap;
import java.util.Map;

/**
* ILP32 and LP64 Architecture, see here: https://unix.org/whitepapers/64bit.html
* Warning note: when deducing type, we assume an ILP32 or an LP64 arch
* (e.g. conversion rules would get more complex, if an int isn't at least twice as big as a short)
*/
 public enum ArchitectureType {
	ILP32(8,16,32,32,32),
	LP64(8,16,32,64,64);

	public final Map<String, Integer> standardTypeSizes = new HashMap<>();

	private ArchitectureType(int _char, int _short, int _int, int _long, int _longlong) {
		standardTypeSizes.put("void", 1);
		standardTypeSizes.put("char", _char);
		standardTypeSizes.put("short", _short);
		standardTypeSizes.put("int", _int);
		standardTypeSizes.put("long", _long);
		standardTypeSizes.put("longlong", _longlong);
	}

	public int getBitWidth(String typeName) {
		return standardTypeSizes.get(typeName);
	}
}