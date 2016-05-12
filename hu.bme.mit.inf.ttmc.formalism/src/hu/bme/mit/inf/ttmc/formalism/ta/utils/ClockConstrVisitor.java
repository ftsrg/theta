package hu.bme.mit.inf.ttmc.formalism.ta.utils;

import hu.bme.mit.inf.ttmc.formalism.ta.constr.AndConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffEqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffGeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffGtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffLeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffLtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.TrueConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitEqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitGeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitGtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitLeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitLtConstr;

public interface ClockConstrVisitor<P, R> {

	public R visit(final TrueConstr constr, final P param);

	public R visit(final UnitLtConstr constr, final P param);

	public R visit(final UnitLeqConstr constr, final P param);

	public R visit(final UnitGtConstr constr, final P param);

	public R visit(final UnitGeqConstr constr, final P param);

	public R visit(final UnitEqConstr constr, final P param);

	public R visit(final DiffLtConstr constr, final P param);

	public R visit(final DiffLeqConstr constr, final P param);

	public R visit(final DiffGtConstr constr, final P param);

	public R visit(final DiffGeqConstr constr, final P param);

	public R visit(final DiffEqConstr constr, final P param);

	public R visit(final AndConstr constr, final P param);

}
