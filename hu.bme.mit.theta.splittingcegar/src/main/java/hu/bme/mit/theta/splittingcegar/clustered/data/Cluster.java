package hu.bme.mit.theta.splittingcegar.clustered.data;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.booltype.BoolType;

/**
 * Represents a cluster of variables and formulas
 */
public class Cluster {
	private final Set<VarDecl<?>> vars;
	private final List<Expr<BoolType>> formulas;
	private int clusterId;

	public Cluster() {
		vars = new HashSet<>();
		formulas = new ArrayList<>();
		clusterId = -1; // ID must be set by the one who creates the cluster
						// using setId()
	}

	public Set<VarDecl<? extends Type>> getVars() {
		return vars;
	}

	public List<Expr<BoolType>> getFormulas() {
		return formulas;
	}

	public int getClusterId() {
		return clusterId;
	}

	public void setId(final int id) {
		this.clusterId = id;
	}

	public int getFormulaCount() {
		return formulas.size();
	}

	@Override
	public String toString() {
		final StringBuilder ret = new StringBuilder("Cluster " + clusterId + ": { Variables: {");
		for (final VarDecl<?> var : vars) {
			ret.append(var.getName()).append(" ");
		}
		ret.append("}, Formulas: {");
		for (final Expr<?> ex : formulas) {
			ret.append(ex.toString()).append(" ");
		}
		return ret.append("} }").toString();
	}
}
