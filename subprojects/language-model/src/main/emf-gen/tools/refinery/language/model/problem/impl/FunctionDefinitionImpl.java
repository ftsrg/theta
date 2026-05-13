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

import tools.refinery.language.model.problem.AnnotatedElement;
import tools.refinery.language.model.problem.AnnotationContainer;
import tools.refinery.language.model.problem.Case;
import tools.refinery.language.model.problem.FunctionDefinition;
import tools.refinery.language.model.problem.NamedElement;
import tools.refinery.language.model.problem.Parameter;
import tools.refinery.language.model.problem.PredicateDefinition;
import tools.refinery.language.model.problem.ProblemPackage;
import tools.refinery.language.model.problem.Relation;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Function Definition</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.impl.FunctionDefinitionImpl#getAnnotations <em>Annotations</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.FunctionDefinitionImpl#getParameters <em>Parameters</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.FunctionDefinitionImpl#getName <em>Name</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.FunctionDefinitionImpl#getCases <em>Cases</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.FunctionDefinitionImpl#getFunctionType <em>Function Type</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.FunctionDefinitionImpl#isShadow <em>Shadow</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.FunctionDefinitionImpl#getComputedValue <em>Computed Value</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.FunctionDefinitionImpl#getDomainPredicate <em>Domain Predicate</em>}</li>
 * </ul>
 *
 * @generated
 */
public class FunctionDefinitionImpl extends ProblemEObjectImpl implements FunctionDefinition
{
	/**
	 * The cached value of the '{@link #getAnnotations() <em>Annotations</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getAnnotations()
	 * @generated
	 * @ordered
	 */
	protected AnnotationContainer annotations;

	/**
	 * The cached value of the '{@link #getParameters() <em>Parameters</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getParameters()
	 * @generated
	 * @ordered
	 */
	protected EList<Parameter> parameters;

	/**
	 * The default value of the '{@link #getName() <em>Name</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getName()
	 * @generated
	 * @ordered
	 */
	protected static final String NAME_EDEFAULT = null;

	/**
	 * The cached value of the '{@link #getName() <em>Name</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getName()
	 * @generated
	 * @ordered
	 */
	protected String name = NAME_EDEFAULT;

	/**
	 * The cached value of the '{@link #getCases() <em>Cases</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getCases()
	 * @generated
	 * @ordered
	 */
	protected EList<Case> cases;

	/**
	 * The cached value of the '{@link #getFunctionType() <em>Function Type</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getFunctionType()
	 * @generated
	 * @ordered
	 */
	protected Relation functionType;

	/**
	 * The default value of the '{@link #isShadow() <em>Shadow</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isShadow()
	 * @generated
	 * @ordered
	 */
	protected static final boolean SHADOW_EDEFAULT = false;

	/**
	 * The cached value of the '{@link #isShadow() <em>Shadow</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isShadow()
	 * @generated
	 * @ordered
	 */
	protected boolean shadow = SHADOW_EDEFAULT;

	/**
	 * The cached value of the '{@link #getComputedValue() <em>Computed Value</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getComputedValue()
	 * @generated
	 * @ordered
	 */
	protected FunctionDefinition computedValue;

	/**
	 * The cached value of the '{@link #getDomainPredicate() <em>Domain Predicate</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getDomainPredicate()
	 * @generated
	 * @ordered
	 */
	protected PredicateDefinition domainPredicate;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected FunctionDefinitionImpl()
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
		return ProblemPackage.Literals.FUNCTION_DEFINITION;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public AnnotationContainer getAnnotations()
	{
		return annotations;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetAnnotations(AnnotationContainer newAnnotations, NotificationChain msgs)
	{
		AnnotationContainer oldAnnotations = annotations;
		annotations = newAnnotations;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, ProblemPackage.FUNCTION_DEFINITION__ANNOTATIONS, oldAnnotations, newAnnotations);
			if (msgs == null) msgs = notification; else msgs.add(notification);
		}
		return msgs;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setAnnotations(AnnotationContainer newAnnotations)
	{
		if (newAnnotations != annotations)
		{
			NotificationChain msgs = null;
			if (annotations != null)
				msgs = ((InternalEObject)annotations).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.FUNCTION_DEFINITION__ANNOTATIONS, null, msgs);
			if (newAnnotations != null)
				msgs = ((InternalEObject)newAnnotations).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.FUNCTION_DEFINITION__ANNOTATIONS, null, msgs);
			msgs = basicSetAnnotations(newAnnotations, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.FUNCTION_DEFINITION__ANNOTATIONS, newAnnotations, newAnnotations));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Parameter> getParameters()
	{
		if (parameters == null)
		{
			parameters = new EObjectContainmentEList<Parameter>(Parameter.class, this, ProblemPackage.FUNCTION_DEFINITION__PARAMETERS);
		}
		return parameters;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String getName()
	{
		return name;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setName(String newName)
	{
		String oldName = name;
		name = newName;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.FUNCTION_DEFINITION__NAME, oldName, name));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Case> getCases()
	{
		if (cases == null)
		{
			cases = new EObjectContainmentEList<Case>(Case.class, this, ProblemPackage.FUNCTION_DEFINITION__CASES);
		}
		return cases;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Relation getFunctionType()
	{
		if (functionType != null && functionType.eIsProxy())
		{
			InternalEObject oldFunctionType = (InternalEObject)functionType;
			functionType = (Relation)eResolveProxy(oldFunctionType);
			if (functionType != oldFunctionType)
			{
				if (eNotificationRequired())
					eNotify(new ENotificationImpl(this, Notification.RESOLVE, ProblemPackage.FUNCTION_DEFINITION__FUNCTION_TYPE, oldFunctionType, functionType));
			}
		}
		return functionType;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Relation basicGetFunctionType()
	{
		return functionType;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setFunctionType(Relation newFunctionType)
	{
		Relation oldFunctionType = functionType;
		functionType = newFunctionType;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.FUNCTION_DEFINITION__FUNCTION_TYPE, oldFunctionType, functionType));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public boolean isShadow()
	{
		return shadow;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setShadow(boolean newShadow)
	{
		boolean oldShadow = shadow;
		shadow = newShadow;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.FUNCTION_DEFINITION__SHADOW, oldShadow, shadow));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public FunctionDefinition getComputedValue()
	{
		return computedValue;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetComputedValue(FunctionDefinition newComputedValue, NotificationChain msgs)
	{
		FunctionDefinition oldComputedValue = computedValue;
		computedValue = newComputedValue;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, ProblemPackage.FUNCTION_DEFINITION__COMPUTED_VALUE, oldComputedValue, newComputedValue);
			if (msgs == null) msgs = notification; else msgs.add(notification);
		}
		return msgs;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setComputedValue(FunctionDefinition newComputedValue)
	{
		if (newComputedValue != computedValue)
		{
			NotificationChain msgs = null;
			if (computedValue != null)
				msgs = ((InternalEObject)computedValue).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.FUNCTION_DEFINITION__COMPUTED_VALUE, null, msgs);
			if (newComputedValue != null)
				msgs = ((InternalEObject)newComputedValue).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.FUNCTION_DEFINITION__COMPUTED_VALUE, null, msgs);
			msgs = basicSetComputedValue(newComputedValue, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.FUNCTION_DEFINITION__COMPUTED_VALUE, newComputedValue, newComputedValue));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public PredicateDefinition getDomainPredicate()
	{
		return domainPredicate;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetDomainPredicate(PredicateDefinition newDomainPredicate, NotificationChain msgs)
	{
		PredicateDefinition oldDomainPredicate = domainPredicate;
		domainPredicate = newDomainPredicate;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, ProblemPackage.FUNCTION_DEFINITION__DOMAIN_PREDICATE, oldDomainPredicate, newDomainPredicate);
			if (msgs == null) msgs = notification; else msgs.add(notification);
		}
		return msgs;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setDomainPredicate(PredicateDefinition newDomainPredicate)
	{
		if (newDomainPredicate != domainPredicate)
		{
			NotificationChain msgs = null;
			if (domainPredicate != null)
				msgs = ((InternalEObject)domainPredicate).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.FUNCTION_DEFINITION__DOMAIN_PREDICATE, null, msgs);
			if (newDomainPredicate != null)
				msgs = ((InternalEObject)newDomainPredicate).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.FUNCTION_DEFINITION__DOMAIN_PREDICATE, null, msgs);
			msgs = basicSetDomainPredicate(newDomainPredicate, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.FUNCTION_DEFINITION__DOMAIN_PREDICATE, newDomainPredicate, newDomainPredicate));
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
			case ProblemPackage.FUNCTION_DEFINITION__ANNOTATIONS:
				return basicSetAnnotations(null, msgs);
			case ProblemPackage.FUNCTION_DEFINITION__PARAMETERS:
				return ((InternalEList<?>)getParameters()).basicRemove(otherEnd, msgs);
			case ProblemPackage.FUNCTION_DEFINITION__CASES:
				return ((InternalEList<?>)getCases()).basicRemove(otherEnd, msgs);
			case ProblemPackage.FUNCTION_DEFINITION__COMPUTED_VALUE:
				return basicSetComputedValue(null, msgs);
			case ProblemPackage.FUNCTION_DEFINITION__DOMAIN_PREDICATE:
				return basicSetDomainPredicate(null, msgs);
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
			case ProblemPackage.FUNCTION_DEFINITION__ANNOTATIONS:
				return getAnnotations();
			case ProblemPackage.FUNCTION_DEFINITION__PARAMETERS:
				return getParameters();
			case ProblemPackage.FUNCTION_DEFINITION__NAME:
				return getName();
			case ProblemPackage.FUNCTION_DEFINITION__CASES:
				return getCases();
			case ProblemPackage.FUNCTION_DEFINITION__FUNCTION_TYPE:
				if (resolve) return getFunctionType();
				return basicGetFunctionType();
			case ProblemPackage.FUNCTION_DEFINITION__SHADOW:
				return isShadow();
			case ProblemPackage.FUNCTION_DEFINITION__COMPUTED_VALUE:
				return getComputedValue();
			case ProblemPackage.FUNCTION_DEFINITION__DOMAIN_PREDICATE:
				return getDomainPredicate();
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
			case ProblemPackage.FUNCTION_DEFINITION__ANNOTATIONS:
				setAnnotations((AnnotationContainer)newValue);
				return;
			case ProblemPackage.FUNCTION_DEFINITION__PARAMETERS:
				getParameters().clear();
				getParameters().addAll((Collection<? extends Parameter>)newValue);
				return;
			case ProblemPackage.FUNCTION_DEFINITION__NAME:
				setName((String)newValue);
				return;
			case ProblemPackage.FUNCTION_DEFINITION__CASES:
				getCases().clear();
				getCases().addAll((Collection<? extends Case>)newValue);
				return;
			case ProblemPackage.FUNCTION_DEFINITION__FUNCTION_TYPE:
				setFunctionType((Relation)newValue);
				return;
			case ProblemPackage.FUNCTION_DEFINITION__SHADOW:
				setShadow((Boolean)newValue);
				return;
			case ProblemPackage.FUNCTION_DEFINITION__COMPUTED_VALUE:
				setComputedValue((FunctionDefinition)newValue);
				return;
			case ProblemPackage.FUNCTION_DEFINITION__DOMAIN_PREDICATE:
				setDomainPredicate((PredicateDefinition)newValue);
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
			case ProblemPackage.FUNCTION_DEFINITION__ANNOTATIONS:
				setAnnotations((AnnotationContainer)null);
				return;
			case ProblemPackage.FUNCTION_DEFINITION__PARAMETERS:
				getParameters().clear();
				return;
			case ProblemPackage.FUNCTION_DEFINITION__NAME:
				setName(NAME_EDEFAULT);
				return;
			case ProblemPackage.FUNCTION_DEFINITION__CASES:
				getCases().clear();
				return;
			case ProblemPackage.FUNCTION_DEFINITION__FUNCTION_TYPE:
				setFunctionType((Relation)null);
				return;
			case ProblemPackage.FUNCTION_DEFINITION__SHADOW:
				setShadow(SHADOW_EDEFAULT);
				return;
			case ProblemPackage.FUNCTION_DEFINITION__COMPUTED_VALUE:
				setComputedValue((FunctionDefinition)null);
				return;
			case ProblemPackage.FUNCTION_DEFINITION__DOMAIN_PREDICATE:
				setDomainPredicate((PredicateDefinition)null);
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
			case ProblemPackage.FUNCTION_DEFINITION__ANNOTATIONS:
				return annotations != null;
			case ProblemPackage.FUNCTION_DEFINITION__PARAMETERS:
				return parameters != null && !parameters.isEmpty();
			case ProblemPackage.FUNCTION_DEFINITION__NAME:
				return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
			case ProblemPackage.FUNCTION_DEFINITION__CASES:
				return cases != null && !cases.isEmpty();
			case ProblemPackage.FUNCTION_DEFINITION__FUNCTION_TYPE:
				return functionType != null;
			case ProblemPackage.FUNCTION_DEFINITION__SHADOW:
				return shadow != SHADOW_EDEFAULT;
			case ProblemPackage.FUNCTION_DEFINITION__COMPUTED_VALUE:
				return computedValue != null;
			case ProblemPackage.FUNCTION_DEFINITION__DOMAIN_PREDICATE:
				return domainPredicate != null;
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
		if (baseClass == AnnotatedElement.class)
		{
			switch (derivedFeatureID)
			{
				case ProblemPackage.FUNCTION_DEFINITION__ANNOTATIONS: return ProblemPackage.ANNOTATED_ELEMENT__ANNOTATIONS;
				default: return -1;
			}
		}
		if (baseClass == NamedElement.class)
		{
			switch (derivedFeatureID)
			{
				case ProblemPackage.FUNCTION_DEFINITION__NAME: return ProblemPackage.NAMED_ELEMENT__NAME;
				default: return -1;
			}
		}
		if (baseClass == Relation.class)
		{
			switch (derivedFeatureID)
			{
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
		if (baseClass == AnnotatedElement.class)
		{
			switch (baseFeatureID)
			{
				case ProblemPackage.ANNOTATED_ELEMENT__ANNOTATIONS: return ProblemPackage.FUNCTION_DEFINITION__ANNOTATIONS;
				default: return -1;
			}
		}
		if (baseClass == NamedElement.class)
		{
			switch (baseFeatureID)
			{
				case ProblemPackage.NAMED_ELEMENT__NAME: return ProblemPackage.FUNCTION_DEFINITION__NAME;
				default: return -1;
			}
		}
		if (baseClass == Relation.class)
		{
			switch (baseFeatureID)
			{
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
		result.append(" (name: ");
		result.append(name);
		result.append(", shadow: ");
		result.append(shadow);
		result.append(')');
		return result.toString();
	}

} //FunctionDefinitionImpl
