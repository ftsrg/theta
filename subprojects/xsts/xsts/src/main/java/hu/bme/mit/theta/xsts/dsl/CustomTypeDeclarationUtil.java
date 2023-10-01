package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.common.dsl.DynamicScope;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.type.enumtype.EnumType;

import java.util.Optional;

public final class CustomTypeDeclarationUtil {

	private CustomTypeDeclarationUtil(){}

	public static void declareTypeWithShortName(DynamicScope currentScope, EnumType enumType, String literal, Env env) {
		Symbol fullNameSymbol = currentScope.resolve(EnumType.makeLongName(enumType, literal)).orElseThrow();
		if (fullNameSymbol instanceof XstsCustomLiteralSymbol fNameCustLitSymbol) {
			var customSymbol = XstsCustomLiteralSymbol.copyWithName(fNameCustLitSymbol, literal);
			Optional<? extends Symbol> optionalSymbol = currentScope.resolve(literal);
			if (optionalSymbol.isPresent()) {
				env.define(optionalSymbol.get(), customSymbol.instantiate());
			} else {
				currentScope.declare(customSymbol);
				env.define(customSymbol, customSymbol.instantiate());
			}
		} else {
			throw new IllegalArgumentException(String.format("%s is not a literal of type %s", literal, enumType.getName()));
		}
	}

}
