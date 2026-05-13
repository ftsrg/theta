/**
 */
package tools.refinery.language.model.problem.impl;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import tools.refinery.language.model.problem.ImplicitVariable;
import tools.refinery.language.model.problem.NamedElement;
import tools.refinery.language.model.problem.ProblemPackage;
import tools.refinery.language.model.problem.Relation;
import tools.refinery.language.model.problem.VariableOrNode;
import tools.refinery.language.model.problem.VariableOrNodeExpr;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Variable Or Node Expr</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.impl.VariableOrNodeExprImpl#getVariableOrNode <em>Variable Or Node</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.VariableOrNodeExprImpl#getSingletonVariable <em>Singleton Variable</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.VariableOrNodeExprImpl#getRelation <em>Relation</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.VariableOrNodeExprImpl#getElement <em>Element</em>}</li>
 * </ul>
 *
 * @generated
 */
public class VariableOrNodeExprImpl extends ExprImpl implements VariableOrNodeExpr
{
	/**
	 * The cached setting delegate for the '{@link #getVariableOrNode() <em>Variable Or Node</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getVariableOrNode()
	 * @generated
	 * @ordered
	 */
	protected EStructuralFeature.Internal.SettingDelegate VARIABLE_OR_NODE__ESETTING_DELEGATE = ((EStructuralFeature.Internal)ProblemPackage.Literals.VARIABLE_OR_NODE_EXPR__VARIABLE_OR_NODE).getSettingDelegate();

	/**
	 * The cached value of the '{@link #getSingletonVariable() <em>Singleton Variable</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getSingletonVariable()
	 * @generated
	 * @ordered
	 */
	protected ImplicitVariable singletonVariable;

	/**
	 * The cached setting delegate for the '{@link #getRelation() <em>Relation</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getRelation()
	 * @generated
	 * @ordered
	 */
	protected EStructuralFeature.Internal.SettingDelegate RELATION__ESETTING_DELEGATE = ((EStructuralFeature.Internal)ProblemPackage.Literals.VARIABLE_OR_NODE_EXPR__RELATION).getSettingDelegate();

	/**
	 * The cached value of the '{@link #getElement() <em>Element</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getElement()
	 * @generated
	 * @ordered
	 */
	protected NamedElement element;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected VariableOrNodeExprImpl()
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
		return ProblemPackage.Literals.VARIABLE_OR_NODE_EXPR;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public VariableOrNode getVariableOrNode()
	{
		return (VariableOrNode)VARIABLE_OR_NODE__ESETTING_DELEGATE.dynamicGet(this, null, 0, true, false);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public VariableOrNode basicGetVariableOrNode()
	{
		return (VariableOrNode)VARIABLE_OR_NODE__ESETTING_DELEGATE.dynamicGet(this, null, 0, false, false);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setVariableOrNode(VariableOrNode newVariableOrNode)
	{
		VARIABLE_OR_NODE__ESETTING_DELEGATE.dynamicSet(this, null, 0, newVariableOrNode);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ImplicitVariable getSingletonVariable()
	{
		return singletonVariable;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetSingletonVariable(ImplicitVariable newSingletonVariable, NotificationChain msgs)
	{
		ImplicitVariable oldSingletonVariable = singletonVariable;
		singletonVariable = newSingletonVariable;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, ProblemPackage.VARIABLE_OR_NODE_EXPR__SINGLETON_VARIABLE, oldSingletonVariable, newSingletonVariable);
			if (msgs == null) msgs = notification; else msgs.add(notification);
		}
		return msgs;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setSingletonVariable(ImplicitVariable newSingletonVariable)
	{
		if (newSingletonVariable != singletonVariable)
		{
			NotificationChain msgs = null;
			if (singletonVariable != null)
				msgs = ((InternalEObject)singletonVariable).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.VARIABLE_OR_NODE_EXPR__SINGLETON_VARIABLE, null, msgs);
			if (newSingletonVariable != null)
				msgs = ((InternalEObject)newSingletonVariable).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.VARIABLE_OR_NODE_EXPR__SINGLETON_VARIABLE, null, msgs);
			msgs = basicSetSingletonVariable(newSingletonVariable, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.VARIABLE_OR_NODE_EXPR__SINGLETON_VARIABLE, newSingletonVariable, newSingletonVariable));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Relation getRelation()
	{
		return (Relation)RELATION__ESETTING_DELEGATE.dynamicGet(this, null, 0, true, false);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Relation basicGetRelation()
	{
		return (Relation)RELATION__ESETTING_DELEGATE.dynamicGet(this, null, 0, false, false);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setRelation(Relation newRelation)
	{
		RELATION__ESETTING_DELEGATE.dynamicSet(this, null, 0, newRelation);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NamedElement getElement()
	{
		if (element != null && element.eIsProxy())
		{
			InternalEObject oldElement = (InternalEObject)element;
			element = (NamedElement)eResolveProxy(oldElement);
			if (element != oldElement)
			{
				if (eNotificationRequired())
					eNotify(new ENotificationImpl(this, Notification.RESOLVE, ProblemPackage.VARIABLE_OR_NODE_EXPR__ELEMENT, oldElement, element));
			}
		}
		return element;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NamedElement basicGetElement()
	{
		return element;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setElement(NamedElement newElement)
	{
		NamedElement oldElement = element;
		element = newElement;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.VARIABLE_OR_NODE_EXPR__ELEMENT, oldElement, element));
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
			case ProblemPackage.VARIABLE_OR_NODE_EXPR__SINGLETON_VARIABLE:
				return basicSetSingletonVariable(null, msgs);
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
			case ProblemPackage.VARIABLE_OR_NODE_EXPR__VARIABLE_OR_NODE:
				if (resolve) return getVariableOrNode();
				return basicGetVariableOrNode();
			case ProblemPackage.VARIABLE_OR_NODE_EXPR__SINGLETON_VARIABLE:
				return getSingletonVariable();
			case ProblemPackage.VARIABLE_OR_NODE_EXPR__RELATION:
				if (resolve) return getRelation();
				return basicGetRelation();
			case ProblemPackage.VARIABLE_OR_NODE_EXPR__ELEMENT:
				if (resolve) return getElement();
				return basicGetElement();
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
			case ProblemPackage.VARIABLE_OR_NODE_EXPR__VARIABLE_OR_NODE:
				setVariableOrNode((VariableOrNode)newValue);
				return;
			case ProblemPackage.VARIABLE_OR_NODE_EXPR__SINGLETON_VARIABLE:
				setSingletonVariable((ImplicitVariable)newValue);
				return;
			case ProblemPackage.VARIABLE_OR_NODE_EXPR__RELATION:
				setRelation((Relation)newValue);
				return;
			case ProblemPackage.VARIABLE_OR_NODE_EXPR__ELEMENT:
				setElement((NamedElement)newValue);
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
			case ProblemPackage.VARIABLE_OR_NODE_EXPR__VARIABLE_OR_NODE:
				setVariableOrNode((VariableOrNode)null);
				return;
			case ProblemPackage.VARIABLE_OR_NODE_EXPR__SINGLETON_VARIABLE:
				setSingletonVariable((ImplicitVariable)null);
				return;
			case ProblemPackage.VARIABLE_OR_NODE_EXPR__RELATION:
				setRelation((Relation)null);
				return;
			case ProblemPackage.VARIABLE_OR_NODE_EXPR__ELEMENT:
				setElement((NamedElement)null);
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
			case ProblemPackage.VARIABLE_OR_NODE_EXPR__VARIABLE_OR_NODE:
				return VARIABLE_OR_NODE__ESETTING_DELEGATE.dynamicIsSet(this, null, 0);
			case ProblemPackage.VARIABLE_OR_NODE_EXPR__SINGLETON_VARIABLE:
				return singletonVariable != null;
			case ProblemPackage.VARIABLE_OR_NODE_EXPR__RELATION:
				return RELATION__ESETTING_DELEGATE.dynamicIsSet(this, null, 0);
			case ProblemPackage.VARIABLE_OR_NODE_EXPR__ELEMENT:
				return element != null;
		}
		return super.eIsSet(featureID);
	}

} //VariableOrNodeExprImpl
