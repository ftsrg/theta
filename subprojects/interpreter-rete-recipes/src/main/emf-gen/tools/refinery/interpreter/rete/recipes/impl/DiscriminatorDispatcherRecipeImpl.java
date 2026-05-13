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

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import tools.refinery.interpreter.rete.recipes.DiscriminatorDispatcherRecipe;
import tools.refinery.interpreter.rete.recipes.RecipesPackage;
import tools.refinery.interpreter.rete.recipes.ReteNodeRecipe;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Discriminator Dispatcher Recipe</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.DiscriminatorDispatcherRecipeImpl#getDiscriminationColumnIndex <em>Discrimination Column Index</em>}</li>
 * </ul>
 *
 * @generated
 */
public class DiscriminatorDispatcherRecipeImpl extends SingleParentNodeRecipeImpl implements DiscriminatorDispatcherRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static final String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * The default value of the '{@link #getDiscriminationColumnIndex() <em>Discrimination Column Index</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getDiscriminationColumnIndex()
	 * @generated
	 * @ordered
	 */
	protected static final int DISCRIMINATION_COLUMN_INDEX_EDEFAULT = 0;

	/**
	 * The cached value of the '{@link #getDiscriminationColumnIndex() <em>Discrimination Column Index</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getDiscriminationColumnIndex()
	 * @generated
	 * @ordered
	 */
	protected int discriminationColumnIndex = DISCRIMINATION_COLUMN_INDEX_EDEFAULT;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected DiscriminatorDispatcherRecipeImpl()
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
		return RecipesPackage.Literals.DISCRIMINATOR_DISPATCHER_RECIPE;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public int getDiscriminationColumnIndex()
	{
		return discriminationColumnIndex;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setDiscriminationColumnIndex(int newDiscriminationColumnIndex)
	{
		int oldDiscriminationColumnIndex = discriminationColumnIndex;
		discriminationColumnIndex = newDiscriminationColumnIndex;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.DISCRIMINATOR_DISPATCHER_RECIPE__DISCRIMINATION_COLUMN_INDEX, oldDiscriminationColumnIndex, discriminationColumnIndex));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public int getArity()
	{
		ReteNodeRecipe _parent = this.getParent();
		return _parent.getArity();
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
			case RecipesPackage.DISCRIMINATOR_DISPATCHER_RECIPE__DISCRIMINATION_COLUMN_INDEX:
				return getDiscriminationColumnIndex();
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
			case RecipesPackage.DISCRIMINATOR_DISPATCHER_RECIPE__DISCRIMINATION_COLUMN_INDEX:
				setDiscriminationColumnIndex((Integer)newValue);
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
			case RecipesPackage.DISCRIMINATOR_DISPATCHER_RECIPE__DISCRIMINATION_COLUMN_INDEX:
				setDiscriminationColumnIndex(DISCRIMINATION_COLUMN_INDEX_EDEFAULT);
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
			case RecipesPackage.DISCRIMINATOR_DISPATCHER_RECIPE__DISCRIMINATION_COLUMN_INDEX:
				return discriminationColumnIndex != DISCRIMINATION_COLUMN_INDEX_EDEFAULT;
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
				case RecipesPackage.RETE_NODE_RECIPE___GET_ARITY: return RecipesPackage.DISCRIMINATOR_DISPATCHER_RECIPE___GET_ARITY;
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
			case RecipesPackage.DISCRIMINATOR_DISPATCHER_RECIPE___GET_ARITY:
				return getArity();
		}
		return super.eInvoke(operationID, arguments);
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
		result.append(" (discriminationColumnIndex: "); //$NON-NLS-1$
		result.append(discriminationColumnIndex);
		result.append(')');
		return result.toString();
	}

} //DiscriminatorDispatcherRecipeImpl
