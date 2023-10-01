package hu.bme.mit.theta.core.type.enumtype;

import hu.bme.mit.theta.core.type.DomainSize;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.abstracttype.Equational;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static com.google.common.base.Preconditions.checkArgument;

public final class EnumType implements Equational<EnumType>, Type {

	public static final String FULLY_QUALIFIED_NAME_SEPARATOR = ".";
	private int counter = 0;
	private final Map<String, Integer> literals;
	private final String name;

	private EnumType(String name, Collection<String> values) {
		this.name = name;
		this.literals = new LinkedHashMap<>();
		values.forEach(value -> literals.put(value, counter++));
	}

	public static EnumType of(String name, Collection<String> values) {
		return new EnumType(name, values);
	}

	public static String makeLongName(String typeName, String literal) {
		return String.format("%s%s%s", typeName, FULLY_QUALIFIED_NAME_SEPARATOR, literal);
	}

	public static String makeLongName(EnumType type, String literal) {
		return makeLongName(type.getName(), literal);
	}

	public static String getShortName(String longName) {
		if (!longName.contains(FULLY_QUALIFIED_NAME_SEPARATOR))
			return longName;
		return longName.substring(longName.indexOf(FULLY_QUALIFIED_NAME_SEPARATOR) + FULLY_QUALIFIED_NAME_SEPARATOR.length());
	}

	@Override
	public DomainSize getDomainSize() {
		return DomainSize.of(literals.size());
	}

	@Override
	public EqExpr<EnumType> Eq(Expr<EnumType> leftOp, Expr<EnumType> rightOp) {
		return EnumEqExpr.of(leftOp, rightOp);
	}

	@Override
	public NeqExpr<EnumType> Neq(Expr<EnumType> leftOp, Expr<EnumType> rightOp) {
		return EnumNeqExpr.of(leftOp, rightOp);
	}

	public Set<String> getValues() {
		return literals.keySet();
	}

	public String getName() {
		return name;
	}

	public int getIntValue(String literal) {
		checkArgument(literals.containsKey(literal), String.format("Enum type %s does not contain literal '%s'", name, literal));
		return literals.get(literal);
	}

}
