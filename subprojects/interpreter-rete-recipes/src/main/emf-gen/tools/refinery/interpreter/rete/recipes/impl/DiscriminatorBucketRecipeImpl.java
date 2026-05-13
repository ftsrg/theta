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

import tools.refinery.interpreter.rete.recipes.DiscriminatorBucketRecipe;
import tools.refinery.interpreter.rete.recipes.RecipesPackage;
import tools.refinery.interpreter.rete.recipes.ReteNodeRecipe;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Discriminator Bucket Recipe</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.DiscriminatorBucketRecipeImpl#getBucketKey <em>Bucket Key</em>}</li>
 * </ul>
 *
 * @generated
 */
public class DiscriminatorBucketRecipeImpl extends SingleParentNodeRecipeImpl implements DiscriminatorBucketRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static final String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * The default value of the '{@link #getBucketKey() <em>Bucket Key</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getBucketKey()
	 * @generated
	 * @ordered
	 */
	protected static final Object BUCKET_KEY_EDEFAULT = null;

	/**
	 * The cached value of the '{@link #getBucketKey() <em>Bucket Key</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getBucketKey()
	 * @generated
	 * @ordered
	 */
	protected Object bucketKey = BUCKET_KEY_EDEFAULT;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected DiscriminatorBucketRecipeImpl()
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
		return RecipesPackage.Literals.DISCRIMINATOR_BUCKET_RECIPE;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object getBucketKey()
	{
		return bucketKey;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setBucketKey(Object newBucketKey)
	{
		Object oldBucketKey = bucketKey;
		bucketKey = newBucketKey;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.DISCRIMINATOR_BUCKET_RECIPE__BUCKET_KEY, oldBucketKey, bucketKey));
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
			case RecipesPackage.DISCRIMINATOR_BUCKET_RECIPE__BUCKET_KEY:
				return getBucketKey();
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
			case RecipesPackage.DISCRIMINATOR_BUCKET_RECIPE__BUCKET_KEY:
				setBucketKey(newValue);
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
			case RecipesPackage.DISCRIMINATOR_BUCKET_RECIPE__BUCKET_KEY:
				setBucketKey(BUCKET_KEY_EDEFAULT);
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
			case RecipesPackage.DISCRIMINATOR_BUCKET_RECIPE__BUCKET_KEY:
				return BUCKET_KEY_EDEFAULT == null ? bucketKey != null : !BUCKET_KEY_EDEFAULT.equals(bucketKey);
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
				case RecipesPackage.RETE_NODE_RECIPE___GET_ARITY: return RecipesPackage.DISCRIMINATOR_BUCKET_RECIPE___GET_ARITY;
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
			case RecipesPackage.DISCRIMINATOR_BUCKET_RECIPE___GET_ARITY:
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
		result.append(" (bucketKey: "); //$NON-NLS-1$
		result.append(bucketKey);
		result.append(')');
		return result.toString();
	}

} //DiscriminatorBucketRecipeImpl
