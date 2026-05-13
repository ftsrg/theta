/**
 */
package tools.refinery.language.model.problem.impl;

import org.eclipse.emf.ecore.EClass;

import tools.refinery.language.model.problem.ProblemPackage;
import tools.refinery.language.model.problem.Relation;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Relation</b></em>'.
 * <!-- end-user-doc -->
 *
 * @generated
 */
public abstract class RelationImpl extends NamedElementImpl implements Relation
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected RelationImpl()
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
		return ProblemPackage.Literals.RELATION;
	}

} //RelationImpl
