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
import org.eclipse.emf.ecore.util.EObjectResolvingEList;
import org.eclipse.emf.ecore.util.InternalEList;

import tools.refinery.language.model.problem.AnnotatedElement;
import tools.refinery.language.model.problem.AnnotationContainer;
import tools.refinery.language.model.problem.Conjunction;
import tools.refinery.language.model.problem.NamedElement;
import tools.refinery.language.model.problem.Parameter;
import tools.refinery.language.model.problem.PredicateDefinition;
import tools.refinery.language.model.problem.PredicateKind;
import tools.refinery.language.model.problem.ProblemPackage;
import tools.refinery.language.model.problem.Relation;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Predicate Definition</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.impl.PredicateDefinitionImpl#getAnnotations <em>Annotations</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.PredicateDefinitionImpl#getParameters <em>Parameters</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.PredicateDefinitionImpl#getName <em>Name</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.PredicateDefinitionImpl#getBodies <em>Bodies</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.PredicateDefinitionImpl#getKind <em>Kind</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.PredicateDefinitionImpl#getComputedValue <em>Computed Value</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.PredicateDefinitionImpl#getSuperSets <em>Super Sets</em>}</li>
 * </ul>
 *
 * @generated
 */
public class PredicateDefinitionImpl extends ProblemEObjectImpl implements PredicateDefinition
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
	 * The cached value of the '{@link #getBodies() <em>Bodies</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getBodies()
	 * @generated
	 * @ordered
	 */
	protected EList<Conjunction> bodies;

	/**
	 * The default value of the '{@link #getKind() <em>Kind</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getKind()
	 * @generated
	 * @ordered
	 */
	protected static final PredicateKind KIND_EDEFAULT = PredicateKind.DEFAULT;

	/**
	 * The cached value of the '{@link #getKind() <em>Kind</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getKind()
	 * @generated
	 * @ordered
	 */
	protected PredicateKind kind = KIND_EDEFAULT;

	/**
	 * The cached value of the '{@link #getComputedValue() <em>Computed Value</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getComputedValue()
	 * @generated
	 * @ordered
	 */
	protected PredicateDefinition computedValue;

	/**
	 * The cached value of the '{@link #getSuperSets() <em>Super Sets</em>}' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getSuperSets()
	 * @generated
	 * @ordered
	 */
	protected EList<Relation> superSets;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected PredicateDefinitionImpl()
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
		return ProblemPackage.Literals.PREDICATE_DEFINITION;
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
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, ProblemPackage.PREDICATE_DEFINITION__ANNOTATIONS, oldAnnotations, newAnnotations);
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
				msgs = ((InternalEObject)annotations).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.PREDICATE_DEFINITION__ANNOTATIONS, null, msgs);
			if (newAnnotations != null)
				msgs = ((InternalEObject)newAnnotations).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.PREDICATE_DEFINITION__ANNOTATIONS, null, msgs);
			msgs = basicSetAnnotations(newAnnotations, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.PREDICATE_DEFINITION__ANNOTATIONS, newAnnotations, newAnnotations));
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
			parameters = new EObjectContainmentEList<Parameter>(Parameter.class, this, ProblemPackage.PREDICATE_DEFINITION__PARAMETERS);
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
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.PREDICATE_DEFINITION__NAME, oldName, name));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Conjunction> getBodies()
	{
		if (bodies == null)
		{
			bodies = new EObjectContainmentEList<Conjunction>(Conjunction.class, this, ProblemPackage.PREDICATE_DEFINITION__BODIES);
		}
		return bodies;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public PredicateKind getKind()
	{
		return kind;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setKind(PredicateKind newKind)
	{
		PredicateKind oldKind = kind;
		kind = newKind == null ? KIND_EDEFAULT : newKind;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.PREDICATE_DEFINITION__KIND, oldKind, kind));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public PredicateDefinition getComputedValue()
	{
		return computedValue;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetComputedValue(PredicateDefinition newComputedValue, NotificationChain msgs)
	{
		PredicateDefinition oldComputedValue = computedValue;
		computedValue = newComputedValue;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, ProblemPackage.PREDICATE_DEFINITION__COMPUTED_VALUE, oldComputedValue, newComputedValue);
			if (msgs == null) msgs = notification; else msgs.add(notification);
		}
		return msgs;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setComputedValue(PredicateDefinition newComputedValue)
	{
		if (newComputedValue != computedValue)
		{
			NotificationChain msgs = null;
			if (computedValue != null)
				msgs = ((InternalEObject)computedValue).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.PREDICATE_DEFINITION__COMPUTED_VALUE, null, msgs);
			if (newComputedValue != null)
				msgs = ((InternalEObject)newComputedValue).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.PREDICATE_DEFINITION__COMPUTED_VALUE, null, msgs);
			msgs = basicSetComputedValue(newComputedValue, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.PREDICATE_DEFINITION__COMPUTED_VALUE, newComputedValue, newComputedValue));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Relation> getSuperSets()
	{
		if (superSets == null)
		{
			superSets = new EObjectResolvingEList<Relation>(Relation.class, this, ProblemPackage.PREDICATE_DEFINITION__SUPER_SETS);
		}
		return superSets;
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
			case ProblemPackage.PREDICATE_DEFINITION__ANNOTATIONS:
				return basicSetAnnotations(null, msgs);
			case ProblemPackage.PREDICATE_DEFINITION__PARAMETERS:
				return ((InternalEList<?>)getParameters()).basicRemove(otherEnd, msgs);
			case ProblemPackage.PREDICATE_DEFINITION__BODIES:
				return ((InternalEList<?>)getBodies()).basicRemove(otherEnd, msgs);
			case ProblemPackage.PREDICATE_DEFINITION__COMPUTED_VALUE:
				return basicSetComputedValue(null, msgs);
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
			case ProblemPackage.PREDICATE_DEFINITION__ANNOTATIONS:
				return getAnnotations();
			case ProblemPackage.PREDICATE_DEFINITION__PARAMETERS:
				return getParameters();
			case ProblemPackage.PREDICATE_DEFINITION__NAME:
				return getName();
			case ProblemPackage.PREDICATE_DEFINITION__BODIES:
				return getBodies();
			case ProblemPackage.PREDICATE_DEFINITION__KIND:
				return getKind();
			case ProblemPackage.PREDICATE_DEFINITION__COMPUTED_VALUE:
				return getComputedValue();
			case ProblemPackage.PREDICATE_DEFINITION__SUPER_SETS:
				return getSuperSets();
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
			case ProblemPackage.PREDICATE_DEFINITION__ANNOTATIONS:
				setAnnotations((AnnotationContainer)newValue);
				return;
			case ProblemPackage.PREDICATE_DEFINITION__PARAMETERS:
				getParameters().clear();
				getParameters().addAll((Collection<? extends Parameter>)newValue);
				return;
			case ProblemPackage.PREDICATE_DEFINITION__NAME:
				setName((String)newValue);
				return;
			case ProblemPackage.PREDICATE_DEFINITION__BODIES:
				getBodies().clear();
				getBodies().addAll((Collection<? extends Conjunction>)newValue);
				return;
			case ProblemPackage.PREDICATE_DEFINITION__KIND:
				setKind((PredicateKind)newValue);
				return;
			case ProblemPackage.PREDICATE_DEFINITION__COMPUTED_VALUE:
				setComputedValue((PredicateDefinition)newValue);
				return;
			case ProblemPackage.PREDICATE_DEFINITION__SUPER_SETS:
				getSuperSets().clear();
				getSuperSets().addAll((Collection<? extends Relation>)newValue);
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
			case ProblemPackage.PREDICATE_DEFINITION__ANNOTATIONS:
				setAnnotations((AnnotationContainer)null);
				return;
			case ProblemPackage.PREDICATE_DEFINITION__PARAMETERS:
				getParameters().clear();
				return;
			case ProblemPackage.PREDICATE_DEFINITION__NAME:
				setName(NAME_EDEFAULT);
				return;
			case ProblemPackage.PREDICATE_DEFINITION__BODIES:
				getBodies().clear();
				return;
			case ProblemPackage.PREDICATE_DEFINITION__KIND:
				setKind(KIND_EDEFAULT);
				return;
			case ProblemPackage.PREDICATE_DEFINITION__COMPUTED_VALUE:
				setComputedValue((PredicateDefinition)null);
				return;
			case ProblemPackage.PREDICATE_DEFINITION__SUPER_SETS:
				getSuperSets().clear();
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
			case ProblemPackage.PREDICATE_DEFINITION__ANNOTATIONS:
				return annotations != null;
			case ProblemPackage.PREDICATE_DEFINITION__PARAMETERS:
				return parameters != null && !parameters.isEmpty();
			case ProblemPackage.PREDICATE_DEFINITION__NAME:
				return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
			case ProblemPackage.PREDICATE_DEFINITION__BODIES:
				return bodies != null && !bodies.isEmpty();
			case ProblemPackage.PREDICATE_DEFINITION__KIND:
				return kind != KIND_EDEFAULT;
			case ProblemPackage.PREDICATE_DEFINITION__COMPUTED_VALUE:
				return computedValue != null;
			case ProblemPackage.PREDICATE_DEFINITION__SUPER_SETS:
				return superSets != null && !superSets.isEmpty();
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
				case ProblemPackage.PREDICATE_DEFINITION__ANNOTATIONS: return ProblemPackage.ANNOTATED_ELEMENT__ANNOTATIONS;
				default: return -1;
			}
		}
		if (baseClass == NamedElement.class)
		{
			switch (derivedFeatureID)
			{
				case ProblemPackage.PREDICATE_DEFINITION__NAME: return ProblemPackage.NAMED_ELEMENT__NAME;
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
				case ProblemPackage.ANNOTATED_ELEMENT__ANNOTATIONS: return ProblemPackage.PREDICATE_DEFINITION__ANNOTATIONS;
				default: return -1;
			}
		}
		if (baseClass == NamedElement.class)
		{
			switch (baseFeatureID)
			{
				case ProblemPackage.NAMED_ELEMENT__NAME: return ProblemPackage.PREDICATE_DEFINITION__NAME;
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
		result.append(", kind: ");
		result.append(kind);
		result.append(')');
		return result.toString();
	}

} //PredicateDefinitionImpl
