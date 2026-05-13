/**
 */
package tools.refinery.language.model.problem.impl;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import tools.refinery.language.model.problem.Multiplicity;
import tools.refinery.language.model.problem.ProblemPackage;
import tools.refinery.language.model.problem.Relation;
import tools.refinery.language.model.problem.TypeScope;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Type Scope</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.impl.TypeScopeImpl#isIncrement <em>Increment</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.TypeScopeImpl#getMultiplicity <em>Multiplicity</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.TypeScopeImpl#getTargetType <em>Target Type</em>}</li>
 * </ul>
 *
 * @generated
 */
public class TypeScopeImpl extends ProblemEObjectImpl implements TypeScope
{
	/**
	 * The default value of the '{@link #isIncrement() <em>Increment</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isIncrement()
	 * @generated
	 * @ordered
	 */
	protected static final boolean INCREMENT_EDEFAULT = false;

	/**
	 * The cached value of the '{@link #isIncrement() <em>Increment</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isIncrement()
	 * @generated
	 * @ordered
	 */
	protected boolean increment = INCREMENT_EDEFAULT;

	/**
	 * The cached value of the '{@link #getMultiplicity() <em>Multiplicity</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getMultiplicity()
	 * @generated
	 * @ordered
	 */
	protected Multiplicity multiplicity;

	/**
	 * The cached value of the '{@link #getTargetType() <em>Target Type</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getTargetType()
	 * @generated
	 * @ordered
	 */
	protected Relation targetType;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected TypeScopeImpl()
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
		return ProblemPackage.Literals.TYPE_SCOPE;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public boolean isIncrement()
	{
		return increment;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setIncrement(boolean newIncrement)
	{
		boolean oldIncrement = increment;
		increment = newIncrement;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.TYPE_SCOPE__INCREMENT, oldIncrement, increment));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Multiplicity getMultiplicity()
	{
		return multiplicity;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetMultiplicity(Multiplicity newMultiplicity, NotificationChain msgs)
	{
		Multiplicity oldMultiplicity = multiplicity;
		multiplicity = newMultiplicity;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, ProblemPackage.TYPE_SCOPE__MULTIPLICITY, oldMultiplicity, newMultiplicity);
			if (msgs == null) msgs = notification; else msgs.add(notification);
		}
		return msgs;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setMultiplicity(Multiplicity newMultiplicity)
	{
		if (newMultiplicity != multiplicity)
		{
			NotificationChain msgs = null;
			if (multiplicity != null)
				msgs = ((InternalEObject)multiplicity).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.TYPE_SCOPE__MULTIPLICITY, null, msgs);
			if (newMultiplicity != null)
				msgs = ((InternalEObject)newMultiplicity).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.TYPE_SCOPE__MULTIPLICITY, null, msgs);
			msgs = basicSetMultiplicity(newMultiplicity, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.TYPE_SCOPE__MULTIPLICITY, newMultiplicity, newMultiplicity));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Relation getTargetType()
	{
		if (targetType != null && targetType.eIsProxy())
		{
			InternalEObject oldTargetType = (InternalEObject)targetType;
			targetType = (Relation)eResolveProxy(oldTargetType);
			if (targetType != oldTargetType)
			{
				if (eNotificationRequired())
					eNotify(new ENotificationImpl(this, Notification.RESOLVE, ProblemPackage.TYPE_SCOPE__TARGET_TYPE, oldTargetType, targetType));
			}
		}
		return targetType;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Relation basicGetTargetType()
	{
		return targetType;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setTargetType(Relation newTargetType)
	{
		Relation oldTargetType = targetType;
		targetType = newTargetType;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.TYPE_SCOPE__TARGET_TYPE, oldTargetType, targetType));
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
			case ProblemPackage.TYPE_SCOPE__MULTIPLICITY:
				return basicSetMultiplicity(null, msgs);
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
			case ProblemPackage.TYPE_SCOPE__INCREMENT:
				return isIncrement();
			case ProblemPackage.TYPE_SCOPE__MULTIPLICITY:
				return getMultiplicity();
			case ProblemPackage.TYPE_SCOPE__TARGET_TYPE:
				if (resolve) return getTargetType();
				return basicGetTargetType();
		}
		return super.eGet(featureID, resolve, coreType);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void eSet(int featureID, Object newValue)
	{
		switch (featureID)
		{
			case ProblemPackage.TYPE_SCOPE__INCREMENT:
				setIncrement((Boolean)newValue);
				return;
			case ProblemPackage.TYPE_SCOPE__MULTIPLICITY:
				setMultiplicity((Multiplicity)newValue);
				return;
			case ProblemPackage.TYPE_SCOPE__TARGET_TYPE:
				setTargetType((Relation)newValue);
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
			case ProblemPackage.TYPE_SCOPE__INCREMENT:
				setIncrement(INCREMENT_EDEFAULT);
				return;
			case ProblemPackage.TYPE_SCOPE__MULTIPLICITY:
				setMultiplicity((Multiplicity)null);
				return;
			case ProblemPackage.TYPE_SCOPE__TARGET_TYPE:
				setTargetType((Relation)null);
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
			case ProblemPackage.TYPE_SCOPE__INCREMENT:
				return increment != INCREMENT_EDEFAULT;
			case ProblemPackage.TYPE_SCOPE__MULTIPLICITY:
				return multiplicity != null;
			case ProblemPackage.TYPE_SCOPE__TARGET_TYPE:
				return targetType != null;
		}
		return super.eIsSet(featureID);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public String toString()
	{
		if (eIsProxy()) return super.toString();

		StringBuilder result = new StringBuilder(super.toString());
		result.append(" (increment: ");
		result.append(increment);
		result.append(')');
		return result.toString();
	}

} //TypeScopeImpl
