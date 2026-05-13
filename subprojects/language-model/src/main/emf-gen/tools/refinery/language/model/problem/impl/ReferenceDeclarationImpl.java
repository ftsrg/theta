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

import org.eclipse.emf.ecore.util.EObjectResolvingEList;

import tools.refinery.language.model.problem.AnnotatedElement;
import tools.refinery.language.model.problem.AnnotationContainer;
import tools.refinery.language.model.problem.Multiplicity;
import tools.refinery.language.model.problem.ProblemPackage;
import tools.refinery.language.model.problem.ReferenceDeclaration;
import tools.refinery.language.model.problem.ReferenceKind;
import tools.refinery.language.model.problem.Relation;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Reference Declaration</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.impl.ReferenceDeclarationImpl#getAnnotations <em>Annotations</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.ReferenceDeclarationImpl#getOpposite <em>Opposite</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.ReferenceDeclarationImpl#getMultiplicity <em>Multiplicity</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.ReferenceDeclarationImpl#getKind <em>Kind</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.ReferenceDeclarationImpl#getReferenceType <em>Reference Type</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.ReferenceDeclarationImpl#getInvalidMultiplicity <em>Invalid Multiplicity</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.ReferenceDeclarationImpl#getSuperSets <em>Super Sets</em>}</li>
 * </ul>
 *
 * @generated
 */
public class ReferenceDeclarationImpl extends RelationImpl implements ReferenceDeclaration
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
	 * The cached value of the '{@link #getOpposite() <em>Opposite</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getOpposite()
	 * @generated
	 * @ordered
	 */
	protected ReferenceDeclaration opposite;

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
	 * The default value of the '{@link #getKind() <em>Kind</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getKind()
	 * @generated
	 * @ordered
	 */
	protected static final ReferenceKind KIND_EDEFAULT = ReferenceKind.DEFAULT;

	/**
	 * The cached value of the '{@link #getKind() <em>Kind</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getKind()
	 * @generated
	 * @ordered
	 */
	protected ReferenceKind kind = KIND_EDEFAULT;

	/**
	 * The cached value of the '{@link #getReferenceType() <em>Reference Type</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getReferenceType()
	 * @generated
	 * @ordered
	 */
	protected Relation referenceType;

	/**
	 * The cached value of the '{@link #getInvalidMultiplicity() <em>Invalid Multiplicity</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getInvalidMultiplicity()
	 * @generated
	 * @ordered
	 */
	protected Relation invalidMultiplicity;

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
	protected ReferenceDeclarationImpl()
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
		return ProblemPackage.Literals.REFERENCE_DECLARATION;
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
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, ProblemPackage.REFERENCE_DECLARATION__ANNOTATIONS, oldAnnotations, newAnnotations);
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
				msgs = ((InternalEObject)annotations).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.REFERENCE_DECLARATION__ANNOTATIONS, null, msgs);
			if (newAnnotations != null)
				msgs = ((InternalEObject)newAnnotations).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.REFERENCE_DECLARATION__ANNOTATIONS, null, msgs);
			msgs = basicSetAnnotations(newAnnotations, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.REFERENCE_DECLARATION__ANNOTATIONS, newAnnotations, newAnnotations));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ReferenceDeclaration getOpposite()
	{
		if (opposite != null && opposite.eIsProxy())
		{
			InternalEObject oldOpposite = (InternalEObject)opposite;
			opposite = (ReferenceDeclaration)eResolveProxy(oldOpposite);
			if (opposite != oldOpposite)
			{
				if (eNotificationRequired())
					eNotify(new ENotificationImpl(this, Notification.RESOLVE, ProblemPackage.REFERENCE_DECLARATION__OPPOSITE, oldOpposite, opposite));
			}
		}
		return opposite;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ReferenceDeclaration basicGetOpposite()
	{
		return opposite;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setOpposite(ReferenceDeclaration newOpposite)
	{
		ReferenceDeclaration oldOpposite = opposite;
		opposite = newOpposite;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.REFERENCE_DECLARATION__OPPOSITE, oldOpposite, opposite));
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
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, ProblemPackage.REFERENCE_DECLARATION__MULTIPLICITY, oldMultiplicity, newMultiplicity);
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
				msgs = ((InternalEObject)multiplicity).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.REFERENCE_DECLARATION__MULTIPLICITY, null, msgs);
			if (newMultiplicity != null)
				msgs = ((InternalEObject)newMultiplicity).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.REFERENCE_DECLARATION__MULTIPLICITY, null, msgs);
			msgs = basicSetMultiplicity(newMultiplicity, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.REFERENCE_DECLARATION__MULTIPLICITY, newMultiplicity, newMultiplicity));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ReferenceKind getKind()
	{
		return kind;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setKind(ReferenceKind newKind)
	{
		ReferenceKind oldKind = kind;
		kind = newKind == null ? KIND_EDEFAULT : newKind;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.REFERENCE_DECLARATION__KIND, oldKind, kind));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Relation getReferenceType()
	{
		if (referenceType != null && referenceType.eIsProxy())
		{
			InternalEObject oldReferenceType = (InternalEObject)referenceType;
			referenceType = (Relation)eResolveProxy(oldReferenceType);
			if (referenceType != oldReferenceType)
			{
				if (eNotificationRequired())
					eNotify(new ENotificationImpl(this, Notification.RESOLVE, ProblemPackage.REFERENCE_DECLARATION__REFERENCE_TYPE, oldReferenceType, referenceType));
			}
		}
		return referenceType;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Relation basicGetReferenceType()
	{
		return referenceType;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setReferenceType(Relation newReferenceType)
	{
		Relation oldReferenceType = referenceType;
		referenceType = newReferenceType;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.REFERENCE_DECLARATION__REFERENCE_TYPE, oldReferenceType, referenceType));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Relation getInvalidMultiplicity()
	{
		return invalidMultiplicity;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetInvalidMultiplicity(Relation newInvalidMultiplicity, NotificationChain msgs)
	{
		Relation oldInvalidMultiplicity = invalidMultiplicity;
		invalidMultiplicity = newInvalidMultiplicity;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, ProblemPackage.REFERENCE_DECLARATION__INVALID_MULTIPLICITY, oldInvalidMultiplicity, newInvalidMultiplicity);
			if (msgs == null) msgs = notification; else msgs.add(notification);
		}
		return msgs;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setInvalidMultiplicity(Relation newInvalidMultiplicity)
	{
		if (newInvalidMultiplicity != invalidMultiplicity)
		{
			NotificationChain msgs = null;
			if (invalidMultiplicity != null)
				msgs = ((InternalEObject)invalidMultiplicity).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.REFERENCE_DECLARATION__INVALID_MULTIPLICITY, null, msgs);
			if (newInvalidMultiplicity != null)
				msgs = ((InternalEObject)newInvalidMultiplicity).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.REFERENCE_DECLARATION__INVALID_MULTIPLICITY, null, msgs);
			msgs = basicSetInvalidMultiplicity(newInvalidMultiplicity, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.REFERENCE_DECLARATION__INVALID_MULTIPLICITY, newInvalidMultiplicity, newInvalidMultiplicity));
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
			superSets = new EObjectResolvingEList<Relation>(Relation.class, this, ProblemPackage.REFERENCE_DECLARATION__SUPER_SETS);
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
			case ProblemPackage.REFERENCE_DECLARATION__ANNOTATIONS:
				return basicSetAnnotations(null, msgs);
			case ProblemPackage.REFERENCE_DECLARATION__MULTIPLICITY:
				return basicSetMultiplicity(null, msgs);
			case ProblemPackage.REFERENCE_DECLARATION__INVALID_MULTIPLICITY:
				return basicSetInvalidMultiplicity(null, msgs);
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
			case ProblemPackage.REFERENCE_DECLARATION__ANNOTATIONS:
				return getAnnotations();
			case ProblemPackage.REFERENCE_DECLARATION__OPPOSITE:
				if (resolve) return getOpposite();
				return basicGetOpposite();
			case ProblemPackage.REFERENCE_DECLARATION__MULTIPLICITY:
				return getMultiplicity();
			case ProblemPackage.REFERENCE_DECLARATION__KIND:
				return getKind();
			case ProblemPackage.REFERENCE_DECLARATION__REFERENCE_TYPE:
				if (resolve) return getReferenceType();
				return basicGetReferenceType();
			case ProblemPackage.REFERENCE_DECLARATION__INVALID_MULTIPLICITY:
				return getInvalidMultiplicity();
			case ProblemPackage.REFERENCE_DECLARATION__SUPER_SETS:
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
			case ProblemPackage.REFERENCE_DECLARATION__ANNOTATIONS:
				setAnnotations((AnnotationContainer)newValue);
				return;
			case ProblemPackage.REFERENCE_DECLARATION__OPPOSITE:
				setOpposite((ReferenceDeclaration)newValue);
				return;
			case ProblemPackage.REFERENCE_DECLARATION__MULTIPLICITY:
				setMultiplicity((Multiplicity)newValue);
				return;
			case ProblemPackage.REFERENCE_DECLARATION__KIND:
				setKind((ReferenceKind)newValue);
				return;
			case ProblemPackage.REFERENCE_DECLARATION__REFERENCE_TYPE:
				setReferenceType((Relation)newValue);
				return;
			case ProblemPackage.REFERENCE_DECLARATION__INVALID_MULTIPLICITY:
				setInvalidMultiplicity((Relation)newValue);
				return;
			case ProblemPackage.REFERENCE_DECLARATION__SUPER_SETS:
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
			case ProblemPackage.REFERENCE_DECLARATION__ANNOTATIONS:
				setAnnotations((AnnotationContainer)null);
				return;
			case ProblemPackage.REFERENCE_DECLARATION__OPPOSITE:
				setOpposite((ReferenceDeclaration)null);
				return;
			case ProblemPackage.REFERENCE_DECLARATION__MULTIPLICITY:
				setMultiplicity((Multiplicity)null);
				return;
			case ProblemPackage.REFERENCE_DECLARATION__KIND:
				setKind(KIND_EDEFAULT);
				return;
			case ProblemPackage.REFERENCE_DECLARATION__REFERENCE_TYPE:
				setReferenceType((Relation)null);
				return;
			case ProblemPackage.REFERENCE_DECLARATION__INVALID_MULTIPLICITY:
				setInvalidMultiplicity((Relation)null);
				return;
			case ProblemPackage.REFERENCE_DECLARATION__SUPER_SETS:
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
			case ProblemPackage.REFERENCE_DECLARATION__ANNOTATIONS:
				return annotations != null;
			case ProblemPackage.REFERENCE_DECLARATION__OPPOSITE:
				return opposite != null;
			case ProblemPackage.REFERENCE_DECLARATION__MULTIPLICITY:
				return multiplicity != null;
			case ProblemPackage.REFERENCE_DECLARATION__KIND:
				return kind != KIND_EDEFAULT;
			case ProblemPackage.REFERENCE_DECLARATION__REFERENCE_TYPE:
				return referenceType != null;
			case ProblemPackage.REFERENCE_DECLARATION__INVALID_MULTIPLICITY:
				return invalidMultiplicity != null;
			case ProblemPackage.REFERENCE_DECLARATION__SUPER_SETS:
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
				case ProblemPackage.REFERENCE_DECLARATION__ANNOTATIONS: return ProblemPackage.ANNOTATED_ELEMENT__ANNOTATIONS;
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
				case ProblemPackage.ANNOTATED_ELEMENT__ANNOTATIONS: return ProblemPackage.REFERENCE_DECLARATION__ANNOTATIONS;
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
		result.append(" (kind: ");
		result.append(kind);
		result.append(')');
		return result.toString();
	}

} //ReferenceDeclarationImpl
