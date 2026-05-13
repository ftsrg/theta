/**
 */
package tools.refinery.language.model.problem.impl;

import java.util.Collection;

import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

import tools.refinery.language.model.problem.Conjunction;
import tools.refinery.language.model.problem.Expr;
import tools.refinery.language.model.problem.ImplicitVariable;
import tools.refinery.language.model.problem.ProblemPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Conjunction</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.impl.ConjunctionImpl#getImplicitVariables <em>Implicit Variables</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.ConjunctionImpl#getLiterals <em>Literals</em>}</li>
 * </ul>
 *
 * @generated
 */
public class ConjunctionImpl extends ProblemEObjectImpl implements Conjunction
{
	/**
	 * The cached value of the '{@link #getImplicitVariables() <em>Implicit Variables</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getImplicitVariables()
	 * @generated
	 * @ordered
	 */
	protected EList<ImplicitVariable> implicitVariables;

	/**
	 * The cached value of the '{@link #getLiterals() <em>Literals</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getLiterals()
	 * @generated
	 * @ordered
	 */
	protected EList<Expr> literals;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected ConjunctionImpl()
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
		return ProblemPackage.Literals.CONJUNCTION;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<ImplicitVariable> getImplicitVariables()
	{
		if (implicitVariables == null)
		{
			implicitVariables = new EObjectContainmentEList<ImplicitVariable>(ImplicitVariable.class, this, ProblemPackage.CONJUNCTION__IMPLICIT_VARIABLES);
		}
		return implicitVariables;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Expr> getLiterals()
	{
		if (literals == null)
		{
			literals = new EObjectContainmentEList<Expr>(Expr.class, this, ProblemPackage.CONJUNCTION__LITERALS);
		}
		return literals;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public NotificationChain eInverseRemove(InternalEObject otherEnd, int featureID, NotificationChain msgs)
	{
		switch (featureID)
		{
			case ProblemPackage.CONJUNCTION__IMPLICIT_VARIABLES:
				return ((InternalEList<?>)getImplicitVariables()).basicRemove(otherEnd, msgs);
			case ProblemPackage.CONJUNCTION__LITERALS:
				return ((InternalEList<?>)getLiterals()).basicRemove(otherEnd, msgs);
		}
		return super.eInverseRemove(otherEnd, featureID, msgs);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object eGet(int featureID, boolean resolve, boolean coreType)
	{
		switch (featureID)
		{
			case ProblemPackage.CONJUNCTION__IMPLICIT_VARIABLES:
				return getImplicitVariables();
			case ProblemPackage.CONJUNCTION__LITERALS:
				return getLiterals();
		}
		return super.eGet(featureID, resolve, coreType);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@SuppressWarnings("unchecked")
	@Override
	public void eSet(int featureID, Object newValue)
	{
		switch (featureID)
		{
			case ProblemPackage.CONJUNCTION__IMPLICIT_VARIABLES:
				getImplicitVariables().clear();
				getImplicitVariables().addAll((Collection<? extends ImplicitVariable>)newValue);
				return;
			case ProblemPackage.CONJUNCTION__LITERALS:
				getLiterals().clear();
				getLiterals().addAll((Collection<? extends Expr>)newValue);
				return;
		}
		super.eSet(featureID, newValue);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void eUnset(int featureID)
	{
		switch (featureID)
		{
			case ProblemPackage.CONJUNCTION__IMPLICIT_VARIABLES:
				getImplicitVariables().clear();
				return;
			case ProblemPackage.CONJUNCTION__LITERALS:
				getLiterals().clear();
				return;
		}
		super.eUnset(featureID);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public boolean eIsSet(int featureID)
	{
		switch (featureID)
		{
			case ProblemPackage.CONJUNCTION__IMPLICIT_VARIABLES:
				return implicitVariables != null && !implicitVariables.isEmpty();
			case ProblemPackage.CONJUNCTION__LITERALS:
				return literals != null && !literals.isEmpty();
		}
		return super.eIsSet(featureID);
	}

} //ConjunctionImpl
