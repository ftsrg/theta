package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xsts.type.XstsCustomType;

import java.util.Objects;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XstsCustomTypeSymbol implements Symbol {

	private XstsCustomType xstsType;

	private XstsCustomTypeSymbol(final XstsCustomType xstsType) {
		this.xstsType =xstsType;
	}

	public static XstsCustomTypeSymbol of(final XstsCustomType xstsType) {
		return new XstsCustomTypeSymbol(xstsType);
	}

	@Override
	public int hashCode() {
		return Objects.hash(xstsType);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof XstsCustomTypeSymbol) {
			final XstsCustomTypeSymbol that = (XstsCustomTypeSymbol) obj;
			return this.xstsType.equals(that.xstsType);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return xstsType.toString();
	}

	public XstsCustomType getXstsType(){
		return xstsType;
	}

	@Override
	public String getName() { return xstsType.getName(); }

	public Type instantiate() {
		return xstsType.getType();
	}
}
