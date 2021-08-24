package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayInitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add;

//TODO: designators
public class CInitializerList extends CStatement{
	private final List<Tuple2<Optional<CStatement>, CStatement>> statements;
	private final CComplexType type;

	public CInitializerList(CComplexType type) {
		this.type = type;
		this.statements = new ArrayList<>();
	}

	@Override
	public Expr<?> getExpression() {
		return getTemplatedExpression();
	}

	@Override
	public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
		return visitor.visit(this, param);
	}

	@SuppressWarnings("unchecked")
	private <I extends Type, E extends Type> Expr<?> getTemplatedExpression() {
		List<Tuple2<Expr<I>, Expr<E>>> list = new ArrayList<>();
		LitExpr<I> currentValue = (LitExpr<I>) CComplexType.getUnsignedLong().getNullValue();
		LitExpr<I> unitValue = (LitExpr<I>) CComplexType.getUnsignedLong().getUnitValue();
		for (Tuple2<Optional<CStatement>, CStatement> cStatement : statements) {
			Expr<E> expr = (Expr<E>) type.castTo(cStatement.get2().getExpression());
			list.add(Tuple2.of(currentValue, expr));
			currentValue = (LitExpr<I>) Add(currentValue, unitValue).eval(ImmutableValuation.empty());
		}
		return ArrayInitExpr.of(list,
				(Expr<E>) type.getNullValue(),
				(ArrayType<I, E>) ArrayType.of(CComplexType.getUnsignedLong().getSmtType(), type.getSmtType()));
	}

	public void addStatement(CStatement index, CStatement value) {
		statements.add(Tuple2.of(Optional.ofNullable(index), value));
	}

	public List<Tuple2<Optional<CStatement>, CStatement>> getStatements() {
		return statements;
	}
}
