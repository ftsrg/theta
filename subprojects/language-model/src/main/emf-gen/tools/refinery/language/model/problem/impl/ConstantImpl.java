/**
 */
package tools.refinery.language.model.problem.impl;

import org.eclipse.emf.ecore.EClass;

import tools.refinery.language.model.problem.Constant;
import tools.refinery.language.model.problem.ProblemPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Constant</b></em>'.
 * <!-- end-user-doc -->
 *
 * @generated
 */
public abstract class ConstantImpl extends ExprImpl implements Constant
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected ConstantImpl()
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
		return ProblemPackage.Literals.CONSTANT;
	}

} //ConstantImpl
