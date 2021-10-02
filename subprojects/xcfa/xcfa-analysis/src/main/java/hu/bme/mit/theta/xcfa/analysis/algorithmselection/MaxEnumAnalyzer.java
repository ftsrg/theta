package hu.bme.mit.theta.xcfa.analysis.algorithmselection;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.abstracttype.LeqExpr;
import hu.bme.mit.theta.core.type.abstracttype.LtExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.utils.BvUtils;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.Optional;

/**
 * Estimates the value boundaries of integer C variables to decide on a value for the configuration option maxEnum
 * Experimental feature, under development
 */
public class MaxEnumAnalyzer {
	public static final MaxEnumAnalyzer instance = new MaxEnumAnalyzer();
	public static boolean enabled = true;

	LinkedHashMap<RefExpr<?>, Tuple2<Optional<BigInteger>, Optional<BigInteger>>> boundaries = new LinkedHashMap<>(); // k: variable ref, v: min, max

	public void consume(Expr<BoolType> relationalExpr) {
		if(!enabled) {
			return;
		}
		LitExpr<?> constant = null;
		RefExpr<?> var = null;

		// check, if it is a constant rel.op var expression or var rel.op constant or neither
		if (relationalExpr.getOps().get(0) instanceof LitExpr) {
			if (relationalExpr.getOps().get(1) instanceof RefExpr) {
				constant = (LitExpr<?>) relationalExpr.getOps().get(0);
				var = (RefExpr<?>) relationalExpr.getOps().get(1);
			}
		} else if (relationalExpr.getOps().get(1) instanceof LitExpr) {
			if (relationalExpr.getOps().get(0) instanceof RefExpr) {
				constant = (LitExpr<?>) relationalExpr.getOps().get(1);
				var = (RefExpr<?>) relationalExpr.getOps().get(0);
			}
		}

		if(constant == null) return; // neither

		// get boundary value
		BigInteger constantValue;
		if(constant instanceof BvLitExpr) { // bitvector arithmetic
			if( ((BvType) constant.getType()).getSigned() ) {
				constantValue = BvUtils.signedBvLitExprToBigInteger((BvLitExpr) constant);
			} else {
				constantValue = BvUtils.unsignedBvLitExprToBigInteger((BvLitExpr) constant);
			}
		} else if(constant instanceof IntLitExpr) { // integer arithmetic
			constantValue = ((IntLitExpr)constant).getValue();
		} else {
			throw new RuntimeException("Type of LitExpr should be either BvType or IntType");
		}

		// add boundaries to hashmap
		if(relationalExpr instanceof LtExpr || relationalExpr instanceof LeqExpr) {
			if(boundaries.containsKey(var)) {
				if(boundaries.get(var).get2().isEmpty() || boundaries.get(var).get2().get().compareTo(constantValue) < 0) {
					boundaries.put(var, Tuple2.of(boundaries.get(var).get1(), Optional.of(constantValue)));
				}
			} else {
				boundaries.put(var, Tuple2.of(Optional.empty(), Optional.of(constantValue)));
			}
		} else {
			if(boundaries.containsKey(var)) {
				if(boundaries.get(var).get1().isEmpty() || boundaries.get(var).get1().get().compareTo(constantValue) > 0) {
					boundaries.put(var, Tuple2.of(Optional.of(constantValue), boundaries.get(var).get2()));
				}
			} else {
				boundaries.put(var, Tuple2.of(Optional.of(constantValue), Optional.empty()));
			}
		}
	}

	public BigInteger estimateMaxEnum() {
		if(!enabled) {
			throw new RuntimeException("Max enum estimation should not be used as it is disabled currently");
		}
		Optional<BigInteger> width = boundaries.values().stream().map(objects -> {
				if(objects.get2().isEmpty() || objects.get1().isEmpty()) {
					return BigInteger.valueOf(1);
				}
				return objects.get2().get().subtract(objects.get1().get());
		}).max(BigInteger::compareTo);

		boundaries.entrySet().forEach(entry -> {
			System.out.println("key: " + entry.getKey());
			if(entry.getValue().get1().isPresent()) {
				System.out.println("min: " + entry.getValue().get1().get());
			} else System.out.println("No min");
			if(entry.getValue().get2().isPresent()) {
				System.out.println("max: " + entry.getValue().get2().get());
			} else System.out.println("No max");
		});

		if(width.isPresent() && width.get().compareTo(BigInteger.valueOf(1)) < 0) {
			width = Optional.of(BigInteger.valueOf(1));
		}
		return width.orElse(BigInteger.valueOf(1));
	}
}
