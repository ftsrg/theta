package hu.bme.mit.theta.analysis.pred;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.core.model.Valuation;

public interface PredPrec extends Prec {

	PredState createState(final Valuation valuation);

}
