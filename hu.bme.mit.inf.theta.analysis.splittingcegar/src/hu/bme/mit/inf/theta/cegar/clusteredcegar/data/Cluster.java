package hu.bme.mit.inf.theta.cegar.clusteredcegar.data;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;

/**
 * Represents a cluster of variables and formulas
 */
public class Cluster {
	private final Set<VarDecl<? extends Type>> vars;
	private final List<Expr<? extends BoolType>> formulas;
	private int clusterId;

	public Cluster() {
		vars = new HashSet<>();
		formulas = new ArrayList<>();
		clusterId = -1; // ID must be set by the one who creates the cluster using setId()
	}

	public Set<VarDecl<? extends Type>> getVars() {
		return vars;
	}

	public List<Expr<? extends BoolType>> getFormulas() {
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
		for (final VarDecl<? extends Type> var : vars) {
			ret.append(var.getName()).append(" ");
		}
		ret.append("}, Formulas: {");
		for (final Expr<? extends Type> ex : formulas) {
			ret.append(ex.toString()).append(" ");
		}
		return ret.append("} }").toString();
	}
}
