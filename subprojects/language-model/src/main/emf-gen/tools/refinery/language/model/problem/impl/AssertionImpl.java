/**
 */
package tools.refinery.language.model.problem.impl;

import java.util.Collection;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

import tools.refinery.language.model.problem.AbstractAssertion;
import tools.refinery.language.model.problem.Assertion;
import tools.refinery.language.model.problem.AssertionArgument;
import tools.refinery.language.model.problem.ExistentialQuantifier;
import tools.refinery.language.model.problem.Expr;
import tools.refinery.language.model.problem.ImplicitVariable;
import tools.refinery.language.model.problem.ProblemPackage;
import tools.refinery.language.model.problem.Relation;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Assertion</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.impl.AssertionImpl#getImplicitVariables <em>Implicit Variables</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.AssertionImpl#getArguments <em>Arguments</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.AssertionImpl#getRelation <em>Relation</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.AssertionImpl#getValue <em>Value</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.AssertionImpl#isDefault <em>Default</em>}</li>
 * </ul>
 *
 * @generated
 */
public class AssertionImpl extends ProblemEObjectImpl implements Assertion
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
	 * The cached value of the '{@link #getArguments() <em>Arguments</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getArguments()
	 * @generated
	 * @ordered
	 */
	protected EList<AssertionArgument> arguments;

	/**
	 * The cached value of the '{@link #getRelation() <em>Relation</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getRelation()
	 * @generated
	 * @ordered
	 */
	protected Relation relation;

	/**
	 * The cached value of the '{@link #getValue() <em>Value</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getValue()
	 * @generated
	 * @ordered
	 */
	protected Expr value;

	/**
	 * The default value of the '{@link #isDefault() <em>Default</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isDefault()
	 * @generated
	 * @ordered
	 */
	protected static final boolean DEFAULT_EDEFAULT = false;

	/**
	 * The cached value of the '{@link #isDefault() <em>Default</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isDefault()
	 * @generated
	 * @ordered
	 */
	protected boolean default_ = DEFAULT_EDEFAULT;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected AssertionImpl()
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
		return ProblemPackage.Literals.ASSERTION;
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
			implicitVariables = new EObjectContainmentEList<ImplicitVariable>(ImplicitVariable.class, this, ProblemPackage.ASSERTION__IMPLICIT_VARIABLES);
		}
		return implicitVariables;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<AssertionArgument> getArguments()
	{
		if (arguments == null)
		{
			arguments = new EObjectContainmentEList<AssertionArgument>(AssertionArgument.class, this, ProblemPackage.ASSERTION__ARGUMENTS);
		}
		return arguments;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Relation getRelation()
	{
		if (relation != null && relation.eIsProxy())
		{
			InternalEObject oldRelation = (InternalEObject)relation;
			relation = (Relation)eResolveProxy(oldRelation);
			if (relation != oldRelation)
			{
				if (eNotificationRequired())
					eNotify(new ENotificationImpl(this, Notification.RESOLVE, ProblemPackage.ASSERTION__RELATION, oldRelation, relation));
			}
		}
		return relation;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Relation basicGetRelation()
	{
		return relation;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setRelation(Relation newRelation)
	{
		Relation oldRelation = relation;
		relation = newRelation;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.ASSERTION__RELATION, oldRelation, relation));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Expr getValue()
	{
		return value;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetValue(Expr newValue, NotificationChain msgs)
	{
		Expr oldValue = value;
		value = newValue;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, ProblemPackage.ASSERTION__VALUE, oldValue, newValue);
			if (msgs == null) msgs = notification; else msgs.add(notification);
		}
		return msgs;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setValue(Expr newValue)
	{
		if (newValue != value)
		{
			NotificationChain msgs = null;
			if (value != null)
				msgs = ((InternalEObject)value).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.ASSERTION__VALUE, null, msgs);
			if (newValue != null)
				msgs = ((InternalEObject)newValue).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.ASSERTION__VALUE, null, msgs);
			msgs = basicSetValue(newValue, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.ASSERTION__VALUE, newValue, newValue));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public boolean isDefault()
	{
		return default_;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setDefault(boolean newDefault)
	{
		boolean oldDefault = default_;
		default_ = newDefault;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.ASSERTION__DEFAULT, oldDefault, default_));
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
			case ProblemPackage.ASSERTION__IMPLICIT_VARIABLES:
				return ((InternalEList<?>)getImplicitVariables()).basicRemove(otherEnd, msgs);
			case ProblemPackage.ASSERTION__ARGUMENTS:
				return ((InternalEList<?>)getArguments()).basicRemove(otherEnd, msgs);
			case ProblemPackage.ASSERTION__VALUE:
				return basicSetValue(null, msgs);
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
			case ProblemPackage.ASSERTION__IMPLICIT_VARIABLES:
				return getImplicitVariables();
			case ProblemPackage.ASSERTION__ARGUMENTS:
				return getArguments();
			case ProblemPackage.ASSERTION__RELATION:
				if (resolve) return getRelation();
				return basicGetRelation();
			case ProblemPackage.ASSERTION__VALUE:
				return getValue();
			case ProblemPackage.ASSERTION__DEFAULT:
				return isDefault();
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
			case ProblemPackage.ASSERTION__IMPLICIT_VARIABLES:
				getImplicitVariables().clear();
				getImplicitVariables().addAll((Collection<? extends ImplicitVariable>)newValue);
				return;
			case ProblemPackage.ASSERTION__ARGUMENTS:
				getArguments().clear();
				getArguments().addAll((Collection<? extends AssertionArgument>)newValue);
				return;
			case ProblemPackage.ASSERTION__RELATION:
				setRelation((Relation)newValue);
				return;
			case ProblemPackage.ASSERTION__VALUE:
				setValue((Expr)newValue);
				return;
			case ProblemPackage.ASSERTION__DEFAULT:
				setDefault((Boolean)newValue);
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
			case ProblemPackage.ASSERTION__IMPLICIT_VARIABLES:
				getImplicitVariables().clear();
				return;
			case ProblemPackage.ASSERTION__ARGUMENTS:
				getArguments().clear();
				return;
			case ProblemPackage.ASSERTION__RELATION:
				setRelation((Relation)null);
				return;
			case ProblemPackage.ASSERTION__VALUE:
				setValue((Expr)null);
				return;
			case ProblemPackage.ASSERTION__DEFAULT:
				setDefault(DEFAULT_EDEFAULT);
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
			case ProblemPackage.ASSERTION__IMPLICIT_VARIABLES:
				return implicitVariables != null && !implicitVariables.isEmpty();
			case ProblemPackage.ASSERTION__ARGUMENTS:
				return arguments != null && !arguments.isEmpty();
			case ProblemPackage.ASSERTION__RELATION:
				return relation != null;
			case ProblemPackage.ASSERTION__VALUE:
				return value != null;
			case ProblemPackage.ASSERTION__DEFAULT:
				return default_ != DEFAULT_EDEFAULT;
		}
		return super.eIsSet(featureID);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public int eBaseStructuralFeatureID(int derivedFeatureID, Class<?> baseClass)
	{
		if (baseClass == ExistentialQuantifier.class)
		{
			switch (derivedFeatureID)
			{
				case ProblemPackage.ASSERTION__IMPLICIT_VARIABLES: return ProblemPackage.EXISTENTIAL_QUANTIFIER__IMPLICIT_VARIABLES;
				default: return -1;
			}
		}
		if (baseClass == AbstractAssertion.class)
		{
			switch (derivedFeatureID)
			{
				case ProblemPackage.ASSERTION__ARGUMENTS: return ProblemPackage.ABSTRACT_ASSERTION__ARGUMENTS;
				case ProblemPackage.ASSERTION__RELATION: return ProblemPackage.ABSTRACT_ASSERTION__RELATION;
				case ProblemPackage.ASSERTION__VALUE: return ProblemPackage.ABSTRACT_ASSERTION__VALUE;
				default: return -1;
			}
		}
		return super.eBaseStructuralFeatureID(derivedFeatureID, baseClass);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public int eDerivedStructuralFeatureID(int baseFeatureID, Class<?> baseClass)
	{
		if (baseClass == ExistentialQuantifier.class)
		{
			switch (baseFeatureID)
			{
				case ProblemPackage.EXISTENTIAL_QUANTIFIER__IMPLICIT_VARIABLES: return ProblemPackage.ASSERTION__IMPLICIT_VARIABLES;
				default: return -1;
			}
		}
		if (baseClass == AbstractAssertion.class)
		{
			switch (baseFeatureID)
			{
				case ProblemPackage.ABSTRACT_ASSERTION__ARGUMENTS: return ProblemPackage.ASSERTION__ARGUMENTS;
				case ProblemPackage.ABSTRACT_ASSERTION__RELATION: return ProblemPackage.ASSERTION__RELATION;
				case ProblemPackage.ABSTRACT_ASSERTION__VALUE: return ProblemPackage.ASSERTION__VALUE;
				default: return -1;
			}
		}
		return super.eDerivedStructuralFeatureID(baseFeatureID, baseClass);
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
		result.append(" (default: ");
		result.append(default_);
		result.append(')');
		return result.toString();
	}

} //AssertionImpl
