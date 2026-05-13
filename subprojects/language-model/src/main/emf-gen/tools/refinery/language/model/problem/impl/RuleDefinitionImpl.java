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
import tools.refinery.language.model.problem.Conjunction;
import tools.refinery.language.model.problem.Consequent;
import tools.refinery.language.model.problem.NamedElement;
import tools.refinery.language.model.problem.Parameter;
import tools.refinery.language.model.problem.ProblemPackage;
import tools.refinery.language.model.problem.RuleDefinition;
import tools.refinery.language.model.problem.RuleKind;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Rule Definition</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.impl.RuleDefinitionImpl#getAnnotations <em>Annotations</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.RuleDefinitionImpl#getParameters <em>Parameters</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.RuleDefinitionImpl#getName <em>Name</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.RuleDefinitionImpl#getConsequents <em>Consequents</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.RuleDefinitionImpl#getPreconditions <em>Preconditions</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.RuleDefinitionImpl#getKind <em>Kind</em>}</li>
 * </ul>
 *
 * @generated
 */
public class RuleDefinitionImpl extends ProblemEObjectImpl implements RuleDefinition
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
	 * The cached value of the '{@link #getConsequents() <em>Consequents</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getConsequents()
	 * @generated
	 * @ordered
	 */
	protected EList<Consequent> consequents;

	/**
	 * The cached value of the '{@link #getPreconditions() <em>Preconditions</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getPreconditions()
	 * @generated
	 * @ordered
	 */
	protected EList<Conjunction> preconditions;

	/**
	 * The default value of the '{@link #getKind() <em>Kind</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getKind()
	 * @generated
	 * @ordered
	 */
	protected static final RuleKind KIND_EDEFAULT = RuleKind.REFINEMENT;

	/**
	 * The cached value of the '{@link #getKind() <em>Kind</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getKind()
	 * @generated
	 * @ordered
	 */
	protected RuleKind kind = KIND_EDEFAULT;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected RuleDefinitionImpl()
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
		return ProblemPackage.Literals.RULE_DEFINITION;
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
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, ProblemPackage.RULE_DEFINITION__ANNOTATIONS, oldAnnotations, newAnnotations);
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
				msgs = ((InternalEObject)annotations).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.RULE_DEFINITION__ANNOTATIONS, null, msgs);
			if (newAnnotations != null)
				msgs = ((InternalEObject)newAnnotations).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.RULE_DEFINITION__ANNOTATIONS, null, msgs);
			msgs = basicSetAnnotations(newAnnotations, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.RULE_DEFINITION__ANNOTATIONS, newAnnotations, newAnnotations));
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
			parameters = new EObjectContainmentEList<Parameter>(Parameter.class, this, ProblemPackage.RULE_DEFINITION__PARAMETERS);
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
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.RULE_DEFINITION__NAME, oldName, name));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Consequent> getConsequents()
	{
		if (consequents == null)
		{
			consequents = new EObjectContainmentEList<Consequent>(Consequent.class, this, ProblemPackage.RULE_DEFINITION__CONSEQUENTS);
		}
		return consequents;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Conjunction> getPreconditions()
	{
		if (preconditions == null)
		{
			preconditions = new EObjectContainmentEList<Conjunction>(Conjunction.class, this, ProblemPackage.RULE_DEFINITION__PRECONDITIONS);
		}
		return preconditions;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public RuleKind getKind()
	{
		return kind;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setKind(RuleKind newKind)
	{
		RuleKind oldKind = kind;
		kind = newKind == null ? KIND_EDEFAULT : newKind;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.RULE_DEFINITION__KIND, oldKind, kind));
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
			case ProblemPackage.RULE_DEFINITION__ANNOTATIONS:
				return basicSetAnnotations(null, msgs);
			case ProblemPackage.RULE_DEFINITION__PARAMETERS:
				return ((InternalEList<?>)getParameters()).basicRemove(otherEnd, msgs);
			case ProblemPackage.RULE_DEFINITION__CONSEQUENTS:
				return ((InternalEList<?>)getConsequents()).basicRemove(otherEnd, msgs);
			case ProblemPackage.RULE_DEFINITION__PRECONDITIONS:
				return ((InternalEList<?>)getPreconditions()).basicRemove(otherEnd, msgs);
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
			case ProblemPackage.RULE_DEFINITION__ANNOTATIONS:
				return getAnnotations();
			case ProblemPackage.RULE_DEFINITION__PARAMETERS:
				return getParameters();
			case ProblemPackage.RULE_DEFINITION__NAME:
				return getName();
			case ProblemPackage.RULE_DEFINITION__CONSEQUENTS:
				return getConsequents();
			case ProblemPackage.RULE_DEFINITION__PRECONDITIONS:
				return getPreconditions();
			case ProblemPackage.RULE_DEFINITION__KIND:
				return getKind();
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
			case ProblemPackage.RULE_DEFINITION__ANNOTATIONS:
				setAnnotations((AnnotationContainer)newValue);
				return;
			case ProblemPackage.RULE_DEFINITION__PARAMETERS:
				getParameters().clear();
				getParameters().addAll((Collection<? extends Parameter>)newValue);
				return;
			case ProblemPackage.RULE_DEFINITION__NAME:
				setName((String)newValue);
				return;
			case ProblemPackage.RULE_DEFINITION__CONSEQUENTS:
				getConsequents().clear();
				getConsequents().addAll((Collection<? extends Consequent>)newValue);
				return;
			case ProblemPackage.RULE_DEFINITION__PRECONDITIONS:
				getPreconditions().clear();
				getPreconditions().addAll((Collection<? extends Conjunction>)newValue);
				return;
			case ProblemPackage.RULE_DEFINITION__KIND:
				setKind((RuleKind)newValue);
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
			case ProblemPackage.RULE_DEFINITION__ANNOTATIONS:
				setAnnotations((AnnotationContainer)null);
				return;
			case ProblemPackage.RULE_DEFINITION__PARAMETERS:
				getParameters().clear();
				return;
			case ProblemPackage.RULE_DEFINITION__NAME:
				setName(NAME_EDEFAULT);
				return;
			case ProblemPackage.RULE_DEFINITION__CONSEQUENTS:
				getConsequents().clear();
				return;
			case ProblemPackage.RULE_DEFINITION__PRECONDITIONS:
				getPreconditions().clear();
				return;
			case ProblemPackage.RULE_DEFINITION__KIND:
				setKind(KIND_EDEFAULT);
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
			case ProblemPackage.RULE_DEFINITION__ANNOTATIONS:
				return annotations != null;
			case ProblemPackage.RULE_DEFINITION__PARAMETERS:
				return parameters != null && !parameters.isEmpty();
			case ProblemPackage.RULE_DEFINITION__NAME:
				return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
			case ProblemPackage.RULE_DEFINITION__CONSEQUENTS:
				return consequents != null && !consequents.isEmpty();
			case ProblemPackage.RULE_DEFINITION__PRECONDITIONS:
				return preconditions != null && !preconditions.isEmpty();
			case ProblemPackage.RULE_DEFINITION__KIND:
				return kind != KIND_EDEFAULT;
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
				case ProblemPackage.RULE_DEFINITION__ANNOTATIONS: return ProblemPackage.ANNOTATED_ELEMENT__ANNOTATIONS;
				default: return -1;
			}
		}
		if (baseClass == NamedElement.class)
		{
			switch (derivedFeatureID)
			{
				case ProblemPackage.RULE_DEFINITION__NAME: return ProblemPackage.NAMED_ELEMENT__NAME;
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
				case ProblemPackage.ANNOTATED_ELEMENT__ANNOTATIONS: return ProblemPackage.RULE_DEFINITION__ANNOTATIONS;
				default: return -1;
			}
		}
		if (baseClass == NamedElement.class)
		{
			switch (baseFeatureID)
			{
				case ProblemPackage.NAMED_ELEMENT__NAME: return ProblemPackage.RULE_DEFINITION__NAME;
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

} //RuleDefinitionImpl
