package hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

/**
 * Represents a cluster of variables and formulas
 *
 * @author Akos
 */
public class Cluster {
	private final Set<VarDecl<? extends Type>> variables; // Map of variables
	private final List<Expr<? extends BoolType>> formulas; // List of formulas
	private int id; // Id

	/**
	 * Constructor
	 */
	public Cluster() {
		variables = new HashSet<>();
		formulas = new ArrayList<>();
		id = -1; // ID must be set by the one who creates the cluster using setId()
	}

	/**
	 * Get the map of variables
	 *
	 * @return Map of variables
	 */
	public Set<VarDecl<? extends Type>> getVariables() {
		return variables;
	}

	/**
	 * Get the list of formulas
	 *
	 * @return List of formulas
	 */
	public List<Expr<? extends BoolType>> getFormulas() {
		return formulas;
	}

	/**
	 * Get the ID of the cluster
	 *
	 * @return ID of the cluster
	 */
	public int getId() {
		return id;
	}

	/**
	 * Set the ID of the cluster
	 *
	 * @param id
	 *            New ID of the cluster
	 */
	public void setId(final int id) {
		this.id = id;
	}

	/**
	 * Get the number of formulas
	 *
	 * @return Number of formulas
	 */
	public int getFormulaCount() {
		return formulas.size();
	}

	@Override
	public String toString() {
		final StringBuilder ret = new StringBuilder("Cluster " + id + ": { Variables: {");
		for (final VarDecl<? extends Type> var : variables) {
			ret.append(var.getName()).append(" ");
		}
		ret.append("}, Formulas: {");
		for (final Expr<? extends Type> ex : formulas) {
			ret.append(ex.toString()).append(" ");
		}
		return ret.append("} }").toString();
	}
}
