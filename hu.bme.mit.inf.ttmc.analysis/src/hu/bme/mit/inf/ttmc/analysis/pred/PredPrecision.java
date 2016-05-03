package hu.bme.mit.inf.ttmc.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

public class PredPrecision implements Precision {
	private final List<Expr<? extends BoolType>> preds;

	public PredPrecision(final Collection<Expr<? extends BoolType>> preds) {
		checkNotNull(preds);
		this.preds = Collections.unmodifiableList(new ArrayList<>(preds));
	}

	public List<Expr<? extends BoolType>> getPreds() {
		return preds;
	}
}
