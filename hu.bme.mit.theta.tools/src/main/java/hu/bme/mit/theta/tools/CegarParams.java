package hu.bme.mit.theta.tools;

import com.beust.jcommander.Parameter;

import hu.bme.mit.theta.tools.ConfigurationBuilder.Domain;
import hu.bme.mit.theta.tools.ConfigurationBuilder.PredSplit;
import hu.bme.mit.theta.tools.ConfigurationBuilder.Refinement;
import hu.bme.mit.theta.tools.ConfigurationBuilder.Search;

public class CegarParams {
	@Parameter(names = { "-d", "--domain" }, description = "Abstract domain", required = true)
	Domain domain;

	@Parameter(names = { "-r", "--refinement" }, description = "Refinement strategy", required = true)
	Refinement refinement;

	@Parameter(names = { "-s", "--search" }, description = "Search strategy")
	Search search = Search.BFS;

	@Parameter(names = { "-ps", "--predsplit" }, description = "Predicate splitting")
	PredSplit predSplit = PredSplit.WHOLE;

	public Domain getDomain() {
		return domain;
	}

	public Refinement getRefinement() {
		return refinement;
	}

	public Search getSearch() {
		return search;
	}

	public PredSplit getPredSplit() {
		return predSplit;
	}
}
