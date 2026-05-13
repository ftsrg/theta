/**
 * Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro
 * Copyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License v. 2.0 which is available at
 * http://www.eclipse.org/legal/epl-v20.html.
 * 
 * SPDX-License-Identifier: EPL-2.0
 */
package tools.refinery.interpreter.rete.recipes.impl;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import tools.refinery.interpreter.rete.recipes.IndexerRecipe;
import tools.refinery.interpreter.rete.recipes.JoinRecipe;
import tools.refinery.interpreter.rete.recipes.Mask;
import tools.refinery.interpreter.rete.recipes.ProjectionIndexerRecipe;
import tools.refinery.interpreter.rete.recipes.RecipesPackage;
import tools.refinery.interpreter.rete.recipes.ReteNodeRecipe;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Join Recipe</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.JoinRecipeImpl#getRightParentComplementaryMask <em>Right Parent Complementary Mask</em>}</li>
 * </ul>
 *
 * @generated
 */
public class JoinRecipeImpl extends BetaRecipeImpl implements JoinRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static final String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * The cached value of the '{@link #getRightParentComplementaryMask() <em>Right Parent Complementary Mask</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getRightParentComplementaryMask()
	 * @generated
	 * @ordered
	 */
	protected Mask rightParentComplementaryMask;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected JoinRecipeImpl()
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
		return RecipesPackage.Literals.JOIN_RECIPE;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Mask getRightParentComplementaryMask()
	{
		return rightParentComplementaryMask;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetRightParentComplementaryMask(Mask newRightParentComplementaryMask, NotificationChain msgs)
	{
		Mask oldRightParentComplementaryMask = rightParentComplementaryMask;
		rightParentComplementaryMask = newRightParentComplementaryMask;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, RecipesPackage.JOIN_RECIPE__RIGHT_PARENT_COMPLEMENTARY_MASK, oldRightParentComplementaryMask, newRightParentComplementaryMask);
			if (msgs == null) msgs = notification; else msgs.add(notification);
		}
		return msgs;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setRightParentComplementaryMask(Mask newRightParentComplementaryMask)
	{
		if (newRightParentComplementaryMask != rightParentComplementaryMask)
		{
			NotificationChain msgs = null;
			if (rightParentComplementaryMask != null)
				msgs = ((InternalEObject)rightParentComplementaryMask).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.JOIN_RECIPE__RIGHT_PARENT_COMPLEMENTARY_MASK, null, msgs);
			if (newRightParentComplementaryMask != null)
				msgs = ((InternalEObject)newRightParentComplementaryMask).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.JOIN_RECIPE__RIGHT_PARENT_COMPLEMENTARY_MASK, null, msgs);
			msgs = basicSetRightParentComplementaryMask(newRightParentComplementaryMask, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.JOIN_RECIPE__RIGHT_PARENT_COMPLEMENTARY_MASK, newRightParentComplementaryMask, newRightParentComplementaryMask));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public int getArity()
	{
		ProjectionIndexerRecipe _leftParent = this.getLeftParent();
		int _arity = _leftParent.getArity();
		IndexerRecipe _rightParent = this.getRightParent();
		int _arity_1 = _rightParent.getArity();
		int _plus = (_arity + _arity_1);
		IndexerRecipe _rightParent_1 = this.getRightParent();
		Mask _mask = _rightParent_1.getMask();
		EList<Integer> _sourceIndices = _mask.getSourceIndices();
		int _size = _sourceIndices.size();
		return (_plus - _size);
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
			case RecipesPackage.JOIN_RECIPE__RIGHT_PARENT_COMPLEMENTARY_MASK:
				return basicSetRightParentComplementaryMask(null, msgs);
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
			case RecipesPackage.JOIN_RECIPE__RIGHT_PARENT_COMPLEMENTARY_MASK:
				return getRightParentComplementaryMask();
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
			case RecipesPackage.JOIN_RECIPE__RIGHT_PARENT_COMPLEMENTARY_MASK:
				setRightParentComplementaryMask((Mask)newValue);
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
			case RecipesPackage.JOIN_RECIPE__RIGHT_PARENT_COMPLEMENTARY_MASK:
				setRightParentComplementaryMask((Mask)null);
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
			case RecipesPackage.JOIN_RECIPE__RIGHT_PARENT_COMPLEMENTARY_MASK:
				return rightParentComplementaryMask != null;
		}
		return super.eIsSet(featureID);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public int eDerivedOperationID(int baseOperationID, Class<?> baseClass)
	{
		if (baseClass == ReteNodeRecipe.class)
		{
			switch (baseOperationID)
			{
				case RecipesPackage.RETE_NODE_RECIPE___GET_ARITY: return RecipesPackage.JOIN_RECIPE___GET_ARITY;
				default: return super.eDerivedOperationID(baseOperationID, baseClass);
			}
		}
		return super.eDerivedOperationID(baseOperationID, baseClass);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object eInvoke(int operationID, EList<?> arguments) throws InvocationTargetException
	{
		switch (operationID)
		{
			case RecipesPackage.JOIN_RECIPE___GET_ARITY:
				return getArity();
		}
		return super.eInvoke(operationID, arguments);
	}

} //JoinRecipeImpl
