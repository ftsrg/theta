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
import tools.refinery.language.model.problem.ClassDeclaration;
import tools.refinery.language.model.problem.NamedElement;
import tools.refinery.language.model.problem.Node;
import tools.refinery.language.model.problem.ProblemPackage;
import tools.refinery.language.model.problem.ReferenceDeclaration;
import tools.refinery.language.model.problem.Relation;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Class Declaration</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.impl.ClassDeclarationImpl#getName <em>Name</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.ClassDeclarationImpl#getAnnotations <em>Annotations</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.ClassDeclarationImpl#isAbstract <em>Abstract</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.ClassDeclarationImpl#getFeatureDeclarations <em>Feature Declarations</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.ClassDeclarationImpl#getNewNode <em>New Node</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.ClassDeclarationImpl#getSuperTypes <em>Super Types</em>}</li>
 * </ul>
 *
 * @generated
 */
public class ClassDeclarationImpl extends ProblemEObjectImpl implements ClassDeclaration
{
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
	 * The cached value of the '{@link #getAnnotations() <em>Annotations</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getAnnotations()
	 * @generated
	 * @ordered
	 */
	protected AnnotationContainer annotations;

	/**
	 * The default value of the '{@link #isAbstract() <em>Abstract</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isAbstract()
	 * @generated
	 * @ordered
	 */
	protected static final boolean ABSTRACT_EDEFAULT = false;

	/**
	 * The cached value of the '{@link #isAbstract() <em>Abstract</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isAbstract()
	 * @generated
	 * @ordered
	 */
	protected boolean abstract_ = ABSTRACT_EDEFAULT;

	/**
	 * The cached value of the '{@link #getFeatureDeclarations() <em>Feature Declarations</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getFeatureDeclarations()
	 * @generated
	 * @ordered
	 */
	protected EList<ReferenceDeclaration> featureDeclarations;

	/**
	 * The cached value of the '{@link #getNewNode() <em>New Node</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getNewNode()
	 * @generated
	 * @ordered
	 */
	protected Node newNode;

	/**
	 * The cached value of the '{@link #getSuperTypes() <em>Super Types</em>}' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getSuperTypes()
	 * @generated
	 * @ordered
	 */
	protected EList<Relation> superTypes;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected ClassDeclarationImpl()
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
		return ProblemPackage.Literals.CLASS_DECLARATION;
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
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.CLASS_DECLARATION__NAME, oldName, name));
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
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, ProblemPackage.CLASS_DECLARATION__ANNOTATIONS, oldAnnotations, newAnnotations);
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
				msgs = ((InternalEObject)annotations).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.CLASS_DECLARATION__ANNOTATIONS, null, msgs);
			if (newAnnotations != null)
				msgs = ((InternalEObject)newAnnotations).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.CLASS_DECLARATION__ANNOTATIONS, null, msgs);
			msgs = basicSetAnnotations(newAnnotations, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.CLASS_DECLARATION__ANNOTATIONS, newAnnotations, newAnnotations));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public boolean isAbstract()
	{
		return abstract_;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setAbstract(boolean newAbstract)
	{
		boolean oldAbstract = abstract_;
		abstract_ = newAbstract;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.CLASS_DECLARATION__ABSTRACT, oldAbstract, abstract_));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<ReferenceDeclaration> getFeatureDeclarations()
	{
		if (featureDeclarations == null)
		{
			featureDeclarations = new EObjectContainmentEList<ReferenceDeclaration>(ReferenceDeclaration.class, this, ProblemPackage.CLASS_DECLARATION__FEATURE_DECLARATIONS);
		}
		return featureDeclarations;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Node getNewNode()
	{
		return newNode;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetNewNode(Node newNewNode, NotificationChain msgs)
	{
		Node oldNewNode = newNode;
		newNode = newNewNode;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, ProblemPackage.CLASS_DECLARATION__NEW_NODE, oldNewNode, newNewNode);
			if (msgs == null) msgs = notification; else msgs.add(notification);
		}
		return msgs;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setNewNode(Node newNewNode)
	{
		if (newNewNode != newNode)
		{
			NotificationChain msgs = null;
			if (newNode != null)
				msgs = ((InternalEObject)newNode).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.CLASS_DECLARATION__NEW_NODE, null, msgs);
			if (newNewNode != null)
				msgs = ((InternalEObject)newNewNode).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.CLASS_DECLARATION__NEW_NODE, null, msgs);
			msgs = basicSetNewNode(newNewNode, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.CLASS_DECLARATION__NEW_NODE, newNewNode, newNewNode));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Relation> getSuperTypes()
	{
		if (superTypes == null)
		{
			superTypes = new EObjectResolvingEList<Relation>(Relation.class, this, ProblemPackage.CLASS_DECLARATION__SUPER_TYPES);
		}
		return superTypes;
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
			case ProblemPackage.CLASS_DECLARATION__ANNOTATIONS:
				return basicSetAnnotations(null, msgs);
			case ProblemPackage.CLASS_DECLARATION__FEATURE_DECLARATIONS:
				return ((InternalEList<?>)getFeatureDeclarations()).basicRemove(otherEnd, msgs);
			case ProblemPackage.CLASS_DECLARATION__NEW_NODE:
				return basicSetNewNode(null, msgs);
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
			case ProblemPackage.CLASS_DECLARATION__NAME:
				return getName();
			case ProblemPackage.CLASS_DECLARATION__ANNOTATIONS:
				return getAnnotations();
			case ProblemPackage.CLASS_DECLARATION__ABSTRACT:
				return isAbstract();
			case ProblemPackage.CLASS_DECLARATION__FEATURE_DECLARATIONS:
				return getFeatureDeclarations();
			case ProblemPackage.CLASS_DECLARATION__NEW_NODE:
				return getNewNode();
			case ProblemPackage.CLASS_DECLARATION__SUPER_TYPES:
				return getSuperTypes();
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
			case ProblemPackage.CLASS_DECLARATION__NAME:
				setName((String)newValue);
				return;
			case ProblemPackage.CLASS_DECLARATION__ANNOTATIONS:
				setAnnotations((AnnotationContainer)newValue);
				return;
			case ProblemPackage.CLASS_DECLARATION__ABSTRACT:
				setAbstract((Boolean)newValue);
				return;
			case ProblemPackage.CLASS_DECLARATION__FEATURE_DECLARATIONS:
				getFeatureDeclarations().clear();
				getFeatureDeclarations().addAll((Collection<? extends ReferenceDeclaration>)newValue);
				return;
			case ProblemPackage.CLASS_DECLARATION__NEW_NODE:
				setNewNode((Node)newValue);
				return;
			case ProblemPackage.CLASS_DECLARATION__SUPER_TYPES:
				getSuperTypes().clear();
				getSuperTypes().addAll((Collection<? extends Relation>)newValue);
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
			case ProblemPackage.CLASS_DECLARATION__NAME:
				setName(NAME_EDEFAULT);
				return;
			case ProblemPackage.CLASS_DECLARATION__ANNOTATIONS:
				setAnnotations((AnnotationContainer)null);
				return;
			case ProblemPackage.CLASS_DECLARATION__ABSTRACT:
				setAbstract(ABSTRACT_EDEFAULT);
				return;
			case ProblemPackage.CLASS_DECLARATION__FEATURE_DECLARATIONS:
				getFeatureDeclarations().clear();
				return;
			case ProblemPackage.CLASS_DECLARATION__NEW_NODE:
				setNewNode((Node)null);
				return;
			case ProblemPackage.CLASS_DECLARATION__SUPER_TYPES:
				getSuperTypes().clear();
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
			case ProblemPackage.CLASS_DECLARATION__NAME:
				return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
			case ProblemPackage.CLASS_DECLARATION__ANNOTATIONS:
				return annotations != null;
			case ProblemPackage.CLASS_DECLARATION__ABSTRACT:
				return abstract_ != ABSTRACT_EDEFAULT;
			case ProblemPackage.CLASS_DECLARATION__FEATURE_DECLARATIONS:
				return featureDeclarations != null && !featureDeclarations.isEmpty();
			case ProblemPackage.CLASS_DECLARATION__NEW_NODE:
				return newNode != null;
			case ProblemPackage.CLASS_DECLARATION__SUPER_TYPES:
				return superTypes != null && !superTypes.isEmpty();
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
		if (baseClass == NamedElement.class)
		{
			switch (derivedFeatureID)
			{
				case ProblemPackage.CLASS_DECLARATION__NAME: return ProblemPackage.NAMED_ELEMENT__NAME;
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
		if (baseClass == AnnotatedElement.class)
		{
			switch (derivedFeatureID)
			{
				case ProblemPackage.CLASS_DECLARATION__ANNOTATIONS: return ProblemPackage.ANNOTATED_ELEMENT__ANNOTATIONS;
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
		if (baseClass == NamedElement.class)
		{
			switch (baseFeatureID)
			{
				case ProblemPackage.NAMED_ELEMENT__NAME: return ProblemPackage.CLASS_DECLARATION__NAME;
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
		if (baseClass == AnnotatedElement.class)
		{
			switch (baseFeatureID)
			{
				case ProblemPackage.ANNOTATED_ELEMENT__ANNOTATIONS: return ProblemPackage.CLASS_DECLARATION__ANNOTATIONS;
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
		result.append(", abstract: ");
		result.append(abstract_);
		result.append(')');
		return result.toString();
	}

} //ClassDeclarationImpl
