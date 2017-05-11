package hu.bme.mit.theta.formalism.sts;

import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.expr.Exprs.Add;
import static hu.bme.mit.theta.core.expr.Exprs.And;
import static hu.bme.mit.theta.core.expr.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.Exprs.Geq;
import static hu.bme.mit.theta.core.expr.Exprs.Int;
import static hu.bme.mit.theta.core.expr.Exprs.Ite;
import static hu.bme.mit.theta.core.expr.Exprs.Leq;
import static hu.bme.mit.theta.core.expr.Exprs.Lt;
import static hu.bme.mit.theta.core.expr.Exprs.Not;
import static hu.bme.mit.theta.core.expr.Exprs.Or;
import static hu.bme.mit.theta.core.expr.Exprs.Prime;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.impl.Types;
import hu.bme.mit.theta.formalism.sts.impl.StsImpl;
import hu.bme.mit.theta.formalism.sts.impl.StsImpl.Builder;

public final class StsInstances {

	private StsInstances() {
	}

	public static STS simpleSTS() {
		final Builder builder = new StsImpl.Builder();
		final VarDecl<IntType> r = Var("r", Types.Int());
		final VarDecl<IntType> x = Var("x", Types.Int());
		final VarDecl<IntType> y = Var("y", Types.Int());

		builder.addInvar(Leq(Int(0), r.getRef()));
		builder.addInvar(Leq(Int(0), x.getRef()));
		builder.addInvar(Leq(Int(0), y.getRef()));
		builder.addInvar(Leq(r.getRef(), Int(1)));
		builder.addInvar(Leq(x.getRef(), Int(2)));
		builder.addInvar(Leq(y.getRef(), Int(2)));

		builder.addInit(Eq(r.getRef(), Int(0)));
		builder.addInit(Eq(x.getRef(), Int(0)));
		builder.addInit(Eq(y.getRef(), Int(1)));

		builder.addTrans(And(Geq(Prime(r.getRef()), Int(0)), Leq(Prime(r.getRef()), Int(1))));
		builder.addTrans(Eq(Prime(x.getRef()), Ite(Eq(r.getRef(), Int(1)), Int(0), Ite(Lt(x.getRef(), y.getRef()),
				Add(x.getRef(), Int(1)), Ite(Eq(x.getRef(), y.getRef()), Int(0), x.getRef())))));
		builder.addTrans(Eq(Prime(y.getRef()),
				Ite(Eq(r.getRef(), Int(1)), Int(0), Ite(And(Eq(x.getRef(), y.getRef()), Not(Eq(y.getRef(), Int(2)))),
						Add(y.getRef(), Int(1)), Ite(Eq(x.getRef(), y.getRef()), Int(0), y.getRef())))));

		builder.setProp(Or(Lt(x.getRef(), y.getRef()), Eq(r.getRef(), Int(1))));

		return builder.build();
	}

}
