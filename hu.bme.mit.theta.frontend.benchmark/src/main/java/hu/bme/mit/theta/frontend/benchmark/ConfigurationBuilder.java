package hu.bme.mit.theta.frontend.benchmark;

import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators;
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators.ArgNodeComparator;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.NullLogger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public abstract class ConfigurationBuilder {
	public enum Domain {
		EXPL, PRED
	};

	public enum Refinement {
		CRAIG_ITP, SEQ_ITP, UNSAT_CORE
	};

	public enum Search {
		BFS(ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())), DFS(
				ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.dfs()));

		public final ArgNodeComparator comparator;

		private Search(final ArgNodeComparator comparator) {
			this.comparator = comparator;
		}

	};

	private Logger logger = NullLogger.getInstance();
	private SolverFactory solverFactory = Z3SolverFactory.getInstace();
	private Domain domain;
	private Refinement refinement;
	private Search search = Search.BFS;

	protected ConfigurationBuilder(final Domain domain, final Refinement refinement) {
		this.domain = domain;
		this.refinement = refinement;
	}

	public Logger getLogger() {
		return logger;
	}

	protected void setLogger(final Logger logger) {
		this.logger = logger;
	}

	public SolverFactory getSolverFactory() {
		return solverFactory;
	}

	protected void setSolverFactory(final SolverFactory solverFactory) {
		this.solverFactory = solverFactory;
	}

	public Domain getDomain() {
		return domain;
	}

	protected void setDomain(final Domain domain) {
		this.domain = domain;
	}

	public Refinement getRefinement() {
		return refinement;
	}

	protected void setRefinement(final Refinement refinement) {
		this.refinement = refinement;
	}

	public Search getSearch() {
		return search;
	}

	protected void setSearch(final Search search) {
		this.search = search;
	}

}
