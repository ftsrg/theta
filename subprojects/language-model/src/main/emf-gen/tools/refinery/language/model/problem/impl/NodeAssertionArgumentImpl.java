/**
 */
package tools.refinery.language.model.problem.impl;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import tools.refinery.language.model.problem.NodeAssertionArgument;
import tools.refinery.language.model.problem.ProblemPackage;
import tools.refinery.language.model.problem.VariableOrNode;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Node Assertion Argument</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.impl.NodeAssertionArgumentImpl#getNode <em>Node</em>}</li>
 * </ul>
 *
 * @generated
 */
public class NodeAssertionArgumentImpl extends AssertionArgumentImpl implements NodeAssertionArgument
{
	/**
	 * The cached value of the '{@link #getNode() <em>Node</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getNode()
	 * @generated
	 * @ordered
	 */
	protected VariableOrNode node;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected NodeAssertionArgumentImpl()
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
		return ProblemPackage.Literals.NODE_ASSERTION_ARGUMENT;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public VariableOrNode getNode()
	{
		if (node != null && node.eIsProxy())
		{
			InternalEObject oldNode = (InternalEObject)node;
			node = (VariableOrNode)eResolveProxy(oldNode);
			if (node != oldNode)
			{
				if (eNotificationRequired())
					eNotify(new ENotificationImpl(this, Notification.RESOLVE, ProblemPackage.NODE_ASSERTION_ARGUMENT__NODE, oldNode, node));
			}
		}
		return node;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public VariableOrNode basicGetNode()
	{
		return node;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setNode(VariableOrNode newNode)
	{
		VariableOrNode oldNode = node;
		node = newNode;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.NODE_ASSERTION_ARGUMENT__NODE, oldNode, node));
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
			case ProblemPackage.NODE_ASSERTION_ARGUMENT__NODE:
				if (resolve) return getNode();
				return basicGetNode();
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
			case ProblemPackage.NODE_ASSERTION_ARGUMENT__NODE:
				setNode((VariableOrNode)newValue);
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
			case ProblemPackage.NODE_ASSERTION_ARGUMENT__NODE:
				setNode((VariableOrNode)null);
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
			case ProblemPackage.NODE_ASSERTION_ARGUMENT__NODE:
				return node != null;
		}
		return super.eIsSet(featureID);
	}

} //NodeAssertionArgumentImpl
