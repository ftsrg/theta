package hu.bme.mit.inf.ttmc.constraint.ui

import com.google.common.collect.ImmutableList
import hu.bme.mit.inf.ttmc.constraint.ConstraintManager
import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl
import hu.bme.mit.inf.ttmc.constraint.expr.Expr
import hu.bme.mit.inf.ttmc.constraint.model.ConstraintSpecification
import hu.bme.mit.inf.ttmc.constraint.type.BoolType
import hu.bme.mit.inf.ttmc.constraint.type.Type
import java.util.ArrayList
import java.util.Collection

import static com.google.common.base.Preconditions.checkNotNull

public class ConstraintModelCreator extends ExprCreator {
	
	private val ConstraintSpecification specification;

	new(ConstraintManager manager, ConstraintSpecification specification) {
		super(manager)
		checkNotNull(specification)
		
		this.specification = specification
		
	}
	
	public def ConstraintModel create() {
		val constraints = new ArrayList<Expr<? extends BoolType>>
		for (basicConstraintDefinition : specification.basicConstraintDefinitions) {
			val expression = basicConstraintDefinition.expression
			val expr = expression.toExpr.withType(BoolType)
			constraints += expr
		}
		val constDecls = constantToConst.values

		val model = new ConstraintModelImpl(constDecls, constraints)
		
		model
	}
	
	//////////////////////////////////////////////////////////////////////
	
	private static class ConstraintModelImpl implements ConstraintModel {
		private val Collection<ConstDecl<? extends Type>> constDecls
		private val Collection<Expr<? extends BoolType>> constraints

		private new(Collection<? extends ConstDecl<? extends Type>> constDecls, Collection<? extends Expr<? extends BoolType>> constraints) {
			this.constDecls = ImmutableList.copyOf(checkNotNull(constDecls));
			this.constraints = ImmutableList.copyOf(checkNotNull(constraints));
		}
	
		override Collection<ConstDecl<? extends Type>> getConstDecls() {
			 constDecls
		}
	
		override Collection<Expr<? extends BoolType>> getConstraints() {
			constraints
		}
	}

}
