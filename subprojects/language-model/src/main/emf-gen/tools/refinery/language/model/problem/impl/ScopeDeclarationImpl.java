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

import tools.refinery.language.model.problem.ProblemPackage;
import tools.refinery.language.model.problem.ScopeDeclaration;
import tools.refinery.language.model.problem.TypeScope;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Scope Declaration</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.impl.ScopeDeclarationImpl#getTypeScopes <em>Type Scopes</em>}</li>
 * </ul>
 *
 * @generated
 */
public class ScopeDeclarationImpl extends ProblemEObjectImpl implements ScopeDeclaration
{
	/**
	 * The cached value of the '{@link #getTypeScopes() <em>Type Scopes</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getTypeScopes()
	 * @generated
	 * @ordered
	 */
	protected EList<TypeScope> typeScopes;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected ScopeDeclarationImpl()
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
		return ProblemPackage.Literals.SCOPE_DECLARATION;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<TypeScope> getTypeScopes()
	{
		if (typeScopes == null)
		{
			typeScopes = new EObjectContainmentEList<TypeScope>(TypeScope.class, this, ProblemPackage.SCOPE_DECLARATION__TYPE_SCOPES);
		}
		return typeScopes;
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
			case ProblemPackage.SCOPE_DECLARATION__TYPE_SCOPES:
				return ((InternalEList<?>)getTypeScopes()).basicRemove(otherEnd, msgs);
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
			case ProblemPackage.SCOPE_DECLARATION__TYPE_SCOPES:
				return getTypeScopes();
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
			case ProblemPackage.SCOPE_DECLARATION__TYPE_SCOPES:
				getTypeScopes().clear();
				getTypeScopes().addAll((Collection<? extends TypeScope>)newValue);
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
			case ProblemPackage.SCOPE_DECLARATION__TYPE_SCOPES:
				getTypeScopes().clear();
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
			case ProblemPackage.SCOPE_DECLARATION__TYPE_SCOPES:
				return typeScopes != null && !typeScopes.isEmpty();
		}
		return super.eIsSet(featureID);
	}

} //ScopeDeclarationImpl
