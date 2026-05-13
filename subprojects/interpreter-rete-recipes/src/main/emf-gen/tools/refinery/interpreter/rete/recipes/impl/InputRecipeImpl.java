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

import tools.refinery.interpreter.rete.recipes.InputRecipe;
import tools.refinery.interpreter.rete.recipes.RecipesPackage;
import tools.refinery.interpreter.rete.recipes.ReteNodeRecipe;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Input Recipe</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.InputRecipeImpl#getInputKey <em>Input Key</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.InputRecipeImpl#getKeyID <em>Key ID</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.InputRecipeImpl#getKeyArity <em>Key Arity</em>}</li>
 * </ul>
 *
 * @generated
 */
public class InputRecipeImpl extends ReteNodeRecipeImpl implements InputRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static final String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * The default value of the '{@link #getInputKey() <em>Input Key</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getInputKey()
	 * @generated
	 * @ordered
	 */
	protected static final Object INPUT_KEY_EDEFAULT = null;

	/**
	 * The cached value of the '{@link #getInputKey() <em>Input Key</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getInputKey()
	 * @generated
	 * @ordered
	 */
	protected Object inputKey = INPUT_KEY_EDEFAULT;

	/**
	 * The default value of the '{@link #getKeyID() <em>Key ID</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getKeyID()
	 * @generated
	 * @ordered
	 */
	protected static final String KEY_ID_EDEFAULT = null;

	/**
	 * The cached value of the '{@link #getKeyID() <em>Key ID</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getKeyID()
	 * @generated
	 * @ordered
	 */
	protected String keyID = KEY_ID_EDEFAULT;

	/**
	 * The default value of the '{@link #getKeyArity() <em>Key Arity</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getKeyArity()
	 * @generated
	 * @ordered
	 */
	protected static final int KEY_ARITY_EDEFAULT = 0;

	/**
	 * The cached value of the '{@link #getKeyArity() <em>Key Arity</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getKeyArity()
	 * @generated
	 * @ordered
	 */
	protected int keyArity = KEY_ARITY_EDEFAULT;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected InputRecipeImpl()
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
		return RecipesPackage.Literals.INPUT_RECIPE;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object getInputKey()
	{
		return inputKey;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setInputKey(Object newInputKey)
	{
		Object oldInputKey = inputKey;
		inputKey = newInputKey;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.INPUT_RECIPE__INPUT_KEY, oldInputKey, inputKey));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public String getKeyID()
	{
		return keyID;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setKeyID(String newKeyID)
	{
		String oldKeyID = keyID;
		keyID = newKeyID;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.INPUT_RECIPE__KEY_ID, oldKeyID, keyID));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public int getKeyArity()
	{
		return keyArity;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setKeyArity(int newKeyArity)
	{
		int oldKeyArity = keyArity;
		keyArity = newKeyArity;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.INPUT_RECIPE__KEY_ARITY, oldKeyArity, keyArity));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public int getArity()
	{
		return getKeyArity();
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
			case RecipesPackage.INPUT_RECIPE__INPUT_KEY:
				return getInputKey();
			case RecipesPackage.INPUT_RECIPE__KEY_ID:
				return getKeyID();
			case RecipesPackage.INPUT_RECIPE__KEY_ARITY:
				return getKeyArity();
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
			case RecipesPackage.INPUT_RECIPE__INPUT_KEY:
				setInputKey(newValue);
				return;
			case RecipesPackage.INPUT_RECIPE__KEY_ID:
				setKeyID((String)newValue);
				return;
			case RecipesPackage.INPUT_RECIPE__KEY_ARITY:
				setKeyArity((Integer)newValue);
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
			case RecipesPackage.INPUT_RECIPE__INPUT_KEY:
				setInputKey(INPUT_KEY_EDEFAULT);
				return;
			case RecipesPackage.INPUT_RECIPE__KEY_ID:
				setKeyID(KEY_ID_EDEFAULT);
				return;
			case RecipesPackage.INPUT_RECIPE__KEY_ARITY:
				setKeyArity(KEY_ARITY_EDEFAULT);
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
			case RecipesPackage.INPUT_RECIPE__INPUT_KEY:
				return INPUT_KEY_EDEFAULT == null ? inputKey != null : !INPUT_KEY_EDEFAULT.equals(inputKey);
			case RecipesPackage.INPUT_RECIPE__KEY_ID:
				return KEY_ID_EDEFAULT == null ? keyID != null : !KEY_ID_EDEFAULT.equals(keyID);
			case RecipesPackage.INPUT_RECIPE__KEY_ARITY:
				return keyArity != KEY_ARITY_EDEFAULT;
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
				case RecipesPackage.RETE_NODE_RECIPE___GET_ARITY: return RecipesPackage.INPUT_RECIPE___GET_ARITY;
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
			case RecipesPackage.INPUT_RECIPE___GET_ARITY:
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
		result.append(" (inputKey: "); //$NON-NLS-1$
		result.append(inputKey);
		result.append(", keyID: "); //$NON-NLS-1$
		result.append(keyID);
		result.append(", keyArity: "); //$NON-NLS-1$
		result.append(keyArity);
		result.append(')');
		return result.toString();
	}

} //InputRecipeImpl
