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

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import tools.refinery.interpreter.rete.recipes.ExpressionDefinition;
import tools.refinery.interpreter.rete.recipes.RecipesPackage;
import tools.refinery.interpreter.rete.recipes.RelationEvaluationRecipe;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Relation Evaluation Recipe</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.RelationEvaluationRecipeImpl#getEvaluator <em>Evaluator</em>}</li>
 * </ul>
 *
 * @since 2.8
 * @generated
 */
public class RelationEvaluationRecipeImpl extends MultiParentNodeRecipeImpl implements RelationEvaluationRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static final String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * The cached value of the '{@link #getEvaluator() <em>Evaluator</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getEvaluator()
	 * @generated
	 * @ordered
	 */
	protected ExpressionDefinition evaluator;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected RelationEvaluationRecipeImpl()
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
		return RecipesPackage.Literals.RELATION_EVALUATION_RECIPE;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public ExpressionDefinition getEvaluator()
	{
		if (evaluator != null && evaluator.eIsProxy())
		{
			InternalEObject oldEvaluator = (InternalEObject)evaluator;
			evaluator = (ExpressionDefinition)eResolveProxy(oldEvaluator);
			if (evaluator != oldEvaluator)
			{
				if (eNotificationRequired())
					eNotify(new ENotificationImpl(this, Notification.RESOLVE, RecipesPackage.RELATION_EVALUATION_RECIPE__EVALUATOR, oldEvaluator, evaluator));
			}
		}
		return evaluator;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ExpressionDefinition basicGetEvaluator()
	{
		return evaluator;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setEvaluator(ExpressionDefinition newEvaluator)
	{
		ExpressionDefinition oldEvaluator = evaluator;
		evaluator = newEvaluator;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.RELATION_EVALUATION_RECIPE__EVALUATOR, oldEvaluator, evaluator));
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
			case RecipesPackage.RELATION_EVALUATION_RECIPE__EVALUATOR:
				if (resolve) return getEvaluator();
				return basicGetEvaluator();
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
			case RecipesPackage.RELATION_EVALUATION_RECIPE__EVALUATOR:
				setEvaluator((ExpressionDefinition)newValue);
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
			case RecipesPackage.RELATION_EVALUATION_RECIPE__EVALUATOR:
				setEvaluator((ExpressionDefinition)null);
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
			case RecipesPackage.RELATION_EVALUATION_RECIPE__EVALUATOR:
				return evaluator != null;
		}
		return super.eIsSet(featureID);
	}

} //RelationEvaluationRecipeImpl
