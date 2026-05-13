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

import org.eclipse.emf.common.util.EMap;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import org.eclipse.emf.ecore.util.EcoreEMap;
import org.eclipse.emf.ecore.util.InternalEList;

import tools.refinery.interpreter.rete.recipes.ExpressionDefinition;
import tools.refinery.interpreter.rete.recipes.ExpressionEnforcerRecipe;
import tools.refinery.interpreter.rete.recipes.RecipesPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Expression Enforcer Recipe</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.ExpressionEnforcerRecipeImpl#getExpression <em>Expression</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.ExpressionEnforcerRecipeImpl#getMappedIndices <em>Mapped Indices</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.ExpressionEnforcerRecipeImpl#isCacheOutput <em>Cache Output</em>}</li>
 * </ul>
 *
 * @generated
 */
public abstract class ExpressionEnforcerRecipeImpl extends AlphaRecipeImpl implements ExpressionEnforcerRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static final String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * The cached value of the '{@link #getExpression() <em>Expression</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getExpression()
	 * @generated
	 * @ordered
	 */
	protected ExpressionDefinition expression;

	/**
	 * The cached value of the '{@link #getMappedIndices() <em>Mapped Indices</em>}' map.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getMappedIndices()
	 * @generated
	 * @ordered
	 */
	protected EMap<String, Integer> mappedIndices;

	/**
	 * The default value of the '{@link #isCacheOutput() <em>Cache Output</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isCacheOutput()
	 * @generated
	 * @ordered
	 */
	protected static final boolean CACHE_OUTPUT_EDEFAULT = false;

	/**
	 * The cached value of the '{@link #isCacheOutput() <em>Cache Output</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isCacheOutput()
	 * @generated
	 * @ordered
	 */
	protected boolean cacheOutput = CACHE_OUTPUT_EDEFAULT;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected ExpressionEnforcerRecipeImpl()
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
		return RecipesPackage.Literals.EXPRESSION_ENFORCER_RECIPE;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public ExpressionDefinition getExpression()
	{
		return expression;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetExpression(ExpressionDefinition newExpression, NotificationChain msgs)
	{
		ExpressionDefinition oldExpression = expression;
		expression = newExpression;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, RecipesPackage.EXPRESSION_ENFORCER_RECIPE__EXPRESSION, oldExpression, newExpression);
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
	public void setExpression(ExpressionDefinition newExpression)
	{
		if (newExpression != expression)
		{
			NotificationChain msgs = null;
			if (expression != null)
				msgs = ((InternalEObject)expression).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.EXPRESSION_ENFORCER_RECIPE__EXPRESSION, null, msgs);
			if (newExpression != null)
				msgs = ((InternalEObject)newExpression).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.EXPRESSION_ENFORCER_RECIPE__EXPRESSION, null, msgs);
			msgs = basicSetExpression(newExpression, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.EXPRESSION_ENFORCER_RECIPE__EXPRESSION, newExpression, newExpression));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EMap<String, Integer> getMappedIndices()
	{
		if (mappedIndices == null)
		{
			mappedIndices = new EcoreEMap<String,Integer>(RecipesPackage.Literals.STRING_INDEX_MAP_ENTRY, StringIndexMapEntryImpl.class, this, RecipesPackage.EXPRESSION_ENFORCER_RECIPE__MAPPED_INDICES);
		}
		return mappedIndices;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public boolean isCacheOutput()
	{
		return cacheOutput;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setCacheOutput(boolean newCacheOutput)
	{
		boolean oldCacheOutput = cacheOutput;
		cacheOutput = newCacheOutput;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.EXPRESSION_ENFORCER_RECIPE__CACHE_OUTPUT, oldCacheOutput, cacheOutput));
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
			case RecipesPackage.EXPRESSION_ENFORCER_RECIPE__EXPRESSION:
				return basicSetExpression(null, msgs);
			case RecipesPackage.EXPRESSION_ENFORCER_RECIPE__MAPPED_INDICES:
				return ((InternalEList<?>)getMappedIndices()).basicRemove(otherEnd, msgs);
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
			case RecipesPackage.EXPRESSION_ENFORCER_RECIPE__EXPRESSION:
				return getExpression();
			case RecipesPackage.EXPRESSION_ENFORCER_RECIPE__MAPPED_INDICES:
				if (coreType) return getMappedIndices();
				else return getMappedIndices().map();
			case RecipesPackage.EXPRESSION_ENFORCER_RECIPE__CACHE_OUTPUT:
				return isCacheOutput();
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
			case RecipesPackage.EXPRESSION_ENFORCER_RECIPE__EXPRESSION:
				setExpression((ExpressionDefinition)newValue);
				return;
			case RecipesPackage.EXPRESSION_ENFORCER_RECIPE__MAPPED_INDICES:
				((EStructuralFeature.Setting)getMappedIndices()).set(newValue);
				return;
			case RecipesPackage.EXPRESSION_ENFORCER_RECIPE__CACHE_OUTPUT:
				setCacheOutput((Boolean)newValue);
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
			case RecipesPackage.EXPRESSION_ENFORCER_RECIPE__EXPRESSION:
				setExpression((ExpressionDefinition)null);
				return;
			case RecipesPackage.EXPRESSION_ENFORCER_RECIPE__MAPPED_INDICES:
				getMappedIndices().clear();
				return;
			case RecipesPackage.EXPRESSION_ENFORCER_RECIPE__CACHE_OUTPUT:
				setCacheOutput(CACHE_OUTPUT_EDEFAULT);
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
			case RecipesPackage.EXPRESSION_ENFORCER_RECIPE__EXPRESSION:
				return expression != null;
			case RecipesPackage.EXPRESSION_ENFORCER_RECIPE__MAPPED_INDICES:
				return mappedIndices != null && !mappedIndices.isEmpty();
			case RecipesPackage.EXPRESSION_ENFORCER_RECIPE__CACHE_OUTPUT:
				return cacheOutput != CACHE_OUTPUT_EDEFAULT;
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
		result.append(" (cacheOutput: "); //$NON-NLS-1$
		result.append(cacheOutput);
		result.append(')');
		return result.toString();
	}

} //ExpressionEnforcerRecipeImpl
