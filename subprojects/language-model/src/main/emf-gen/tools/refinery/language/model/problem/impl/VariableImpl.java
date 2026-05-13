/**
 */
package tools.refinery.language.model.problem.impl;

import org.eclipse.emf.ecore.EClass;

import tools.refinery.language.model.problem.ProblemPackage;
import tools.refinery.language.model.problem.Variable;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Variable</b></em>'.
 * <!-- end-user-doc -->
 *
 * @generated
 */
public abstract class VariableImpl extends VariableOrNodeImpl implements Variable
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected VariableImpl()
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
		return ProblemPackage.Literals.VARIABLE;
	}

} //VariableImpl
