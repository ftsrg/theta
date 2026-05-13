/**
 */
package tools.refinery.language.model.problem.impl;

import org.eclipse.emf.ecore.EClass;

import tools.refinery.language.model.problem.ProblemPackage;
import tools.refinery.language.model.problem.RangeExpr;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Range Expr</b></em>'.
 * <!-- end-user-doc -->
 *
 * @generated
 */
public class RangeExprImpl extends BinaryExprImpl implements RangeExpr
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected RangeExprImpl()
	{
		super();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected EClass eStaticClass()
	{
		return ProblemPackage.Literals.RANGE_EXPR;
	}

} //RangeExprImpl
