package hu.bme.mit.theta.xcfa.model.utils;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;

import java.lang.reflect.TypeVariable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;

/**
 * This utility class helps with the awful state of generics in Java.
 * In particular, this solves the problem that equality among type parameters is not runtime checkable in functions.
 */
public class ExpressionReplacer<T extends Type, R extends Type> {
	public static <T extends Type, R extends Type> Optional<Expr<T>> replace(Expr<T> expr, Function<Expr<?>, Optional<Expr<R>>> mapper) {
		return new ExpressionReplacer<T, R>().replaceExpr(expr, mapper);
	}

	private Optional<Expr<T>> replaceExpr(Expr<T> expr, Function<Expr<?>, Optional<Expr<R>>> mapper) {
		if(Arrays.stream(getClass().getTypeParameters()).map(TypeVariable::getGenericDeclaration).distinct().count() == 1) {
			Optional<Expr<R>> transformed = mapper.apply(expr);
			if(transformed.isPresent()) return Optional.of((Expr<T>)transformed.get());
		}
		boolean needsTransformation = false;
		List<Expr<?>> ops = new ArrayList<>();
		for (Expr<?> op : expr.getOps()) {
			Optional<? extends Expr<?>> replace = replace(op, mapper);
			if(replace.isPresent()) {
				needsTransformation = true;
				ops.add(replace.get());
			}
			else {
				ops.add(op);
			}
		}
		if(needsTransformation) {
			Expr<T> tExpr = expr.withOps(ops);
			Map<String, ?> keyMap = FrontendMetadata.lookupMetadata(expr);
			if(keyMap != null) {
				CComplexType cType = (CComplexType) keyMap.get("cType");
				if(cType != null) {
					FrontendMetadata.create(tExpr, "cType", cType);
				}
			}
			return Optional.of(tExpr);
		}
		else return Optional.empty();
	}
}
