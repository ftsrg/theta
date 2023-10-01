package hu.bme.mit.theta.core.type.enumtype;

import com.google.common.base.Objects;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

public final class EnumLitExpr extends NullaryExpr<EnumType> implements LitExpr<EnumType> {

	private final EnumType type;
	private final String value;

	private EnumLitExpr(EnumType type, String value) {
		this.type = type;
		this.value = value;
	}

	public static EnumLitExpr of(EnumType type, String literalName) {
		String value = literalName.contains(".") ? literalName.substring(literalName.indexOf(".") + 1) : literalName;
		checkArgument(type.getValues().contains(value), "Invalid value %s for type %s", value, type.getName());
		return new EnumLitExpr(type, value);
	}

	@Override
	public EnumType getType() {
		return type;
	}

	public String getValue() {
		return value;
	}

	@Override
	public LitExpr<EnumType> eval(Valuation val) {
		return this;
	}

	@Override
	public String toString() {
		return EnumType.makeLongName(type.getName(), value);
	}

	public static BoolLitExpr eq(EnumLitExpr l, EnumLitExpr r) {
		return Bool(l.type.equals(r.type) && l.value.equals(r.value));
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		EnumLitExpr that = (EnumLitExpr) o;
		return Objects.equal(type, that.type) && Objects.equal(value, that.value);
	}

	@Override
	public int hashCode() {
		return Objects.hashCode(type, value);
	}
}
