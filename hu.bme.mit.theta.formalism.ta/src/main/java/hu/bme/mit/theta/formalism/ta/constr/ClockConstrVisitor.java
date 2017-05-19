package hu.bme.mit.theta.formalism.ta.constr;

public interface ClockConstrVisitor<P, R> {

	R visit(final TrueConstr constr, final P param);

	R visit(final FalseConstr constr, final P param);

	R visit(final UnitLtConstr constr, final P param);

	R visit(final UnitLeqConstr constr, final P param);

	R visit(final UnitGtConstr constr, final P param);

	R visit(final UnitGeqConstr constr, final P param);

	R visit(final UnitEqConstr constr, final P param);

	R visit(final DiffLtConstr constr, final P param);

	R visit(final DiffLeqConstr constr, final P param);

	R visit(final DiffGtConstr constr, final P param);

	R visit(final DiffGeqConstr constr, final P param);

	R visit(final DiffEqConstr constr, final P param);

	R visit(final AndConstr constr, final P param);

}
