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

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import tools.refinery.interpreter.rete.recipes.InputFilterRecipe;
import tools.refinery.interpreter.rete.recipes.Mask;
import tools.refinery.interpreter.rete.recipes.RecipesPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Input Filter Recipe</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.InputFilterRecipeImpl#getInputKey <em>Input Key</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.InputFilterRecipeImpl#getKeyID <em>Key ID</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.InputFilterRecipeImpl#getMask <em>Mask</em>}</li>
 * </ul>
 *
 * @generated
 */
public class InputFilterRecipeImpl extends FilterRecipeImpl implements InputFilterRecipe
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
	 * The cached value of the '{@link #getMask() <em>Mask</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getMask()
	 * @generated
	 * @ordered
	 */
	protected Mask mask;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected InputFilterRecipeImpl()
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
		return RecipesPackage.Literals.INPUT_FILTER_RECIPE;
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
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.INPUT_FILTER_RECIPE__INPUT_KEY, oldInputKey, inputKey));
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
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.INPUT_FILTER_RECIPE__KEY_ID, oldKeyID, keyID));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Mask getMask()
	{
		return mask;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetMask(Mask newMask, NotificationChain msgs)
	{
		Mask oldMask = mask;
		mask = newMask;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, RecipesPackage.INPUT_FILTER_RECIPE__MASK, oldMask, newMask);
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
	public void setMask(Mask newMask)
	{
		if (newMask != mask)
		{
			NotificationChain msgs = null;
			if (mask != null)
				msgs = ((InternalEObject)mask).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.INPUT_FILTER_RECIPE__MASK, null, msgs);
			if (newMask != null)
				msgs = ((InternalEObject)newMask).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.INPUT_FILTER_RECIPE__MASK, null, msgs);
			msgs = basicSetMask(newMask, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.INPUT_FILTER_RECIPE__MASK, newMask, newMask));
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
			case RecipesPackage.INPUT_FILTER_RECIPE__MASK:
				return basicSetMask(null, msgs);
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
			case RecipesPackage.INPUT_FILTER_RECIPE__INPUT_KEY:
				return getInputKey();
			case RecipesPackage.INPUT_FILTER_RECIPE__KEY_ID:
				return getKeyID();
			case RecipesPackage.INPUT_FILTER_RECIPE__MASK:
				return getMask();
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
			case RecipesPackage.INPUT_FILTER_RECIPE__INPUT_KEY:
				setInputKey(newValue);
				return;
			case RecipesPackage.INPUT_FILTER_RECIPE__KEY_ID:
				setKeyID((String)newValue);
				return;
			case RecipesPackage.INPUT_FILTER_RECIPE__MASK:
				setMask((Mask)newValue);
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
			case RecipesPackage.INPUT_FILTER_RECIPE__INPUT_KEY:
				setInputKey(INPUT_KEY_EDEFAULT);
				return;
			case RecipesPackage.INPUT_FILTER_RECIPE__KEY_ID:
				setKeyID(KEY_ID_EDEFAULT);
				return;
			case RecipesPackage.INPUT_FILTER_RECIPE__MASK:
				setMask((Mask)null);
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
			case RecipesPackage.INPUT_FILTER_RECIPE__INPUT_KEY:
				return INPUT_KEY_EDEFAULT == null ? inputKey != null : !INPUT_KEY_EDEFAULT.equals(inputKey);
			case RecipesPackage.INPUT_FILTER_RECIPE__KEY_ID:
				return KEY_ID_EDEFAULT == null ? keyID != null : !KEY_ID_EDEFAULT.equals(keyID);
			case RecipesPackage.INPUT_FILTER_RECIPE__MASK:
				return mask != null;
		}
		return super.eIsSet(featureID);
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
		result.append(')');
		return result.toString();
	}

} //InputFilterRecipeImpl
