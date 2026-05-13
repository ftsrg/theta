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

import tools.refinery.interpreter.rete.recipes.MonotonicityInfo;
import tools.refinery.interpreter.rete.recipes.RecipesPackage;
import tools.refinery.interpreter.rete.recipes.RederivableNodeRecipe;
import tools.refinery.interpreter.rete.recipes.UniquenessEnforcerRecipe;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Uniqueness Enforcer Recipe</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.UniquenessEnforcerRecipeImpl#isDeleteRederiveEvaluation <em>Delete Rederive Evaluation</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.UniquenessEnforcerRecipeImpl#getOptionalMonotonicityInfo <em>Optional Monotonicity Info</em>}</li>
 * </ul>
 *
 * @generated
 */
public class UniquenessEnforcerRecipeImpl extends MultiParentNodeRecipeImpl implements UniquenessEnforcerRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static final String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * The default value of the '{@link #isDeleteRederiveEvaluation() <em>Delete Rederive Evaluation</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isDeleteRederiveEvaluation()
	 * @generated
	 * @ordered
	 */
	protected static final boolean DELETE_REDERIVE_EVALUATION_EDEFAULT = false;

	/**
	 * The cached value of the '{@link #isDeleteRederiveEvaluation() <em>Delete Rederive Evaluation</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isDeleteRederiveEvaluation()
	 * @generated
	 * @ordered
	 */
	protected boolean deleteRederiveEvaluation = DELETE_REDERIVE_EVALUATION_EDEFAULT;

	/**
	 * The cached value of the '{@link #getOptionalMonotonicityInfo() <em>Optional Monotonicity Info</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getOptionalMonotonicityInfo()
	 * @generated
	 * @ordered
	 */
	protected MonotonicityInfo optionalMonotonicityInfo;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected UniquenessEnforcerRecipeImpl()
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
		return RecipesPackage.Literals.UNIQUENESS_ENFORCER_RECIPE;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public boolean isDeleteRederiveEvaluation()
	{
		return deleteRederiveEvaluation;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setDeleteRederiveEvaluation(boolean newDeleteRederiveEvaluation)
	{
		boolean oldDeleteRederiveEvaluation = deleteRederiveEvaluation;
		deleteRederiveEvaluation = newDeleteRederiveEvaluation;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__DELETE_REDERIVE_EVALUATION, oldDeleteRederiveEvaluation, deleteRederiveEvaluation));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public MonotonicityInfo getOptionalMonotonicityInfo()
	{
		if (optionalMonotonicityInfo != null && optionalMonotonicityInfo.eIsProxy())
		{
			InternalEObject oldOptionalMonotonicityInfo = (InternalEObject)optionalMonotonicityInfo;
			optionalMonotonicityInfo = (MonotonicityInfo)eResolveProxy(oldOptionalMonotonicityInfo);
			if (optionalMonotonicityInfo != oldOptionalMonotonicityInfo)
			{
				InternalEObject newOptionalMonotonicityInfo = (InternalEObject)optionalMonotonicityInfo;
				NotificationChain msgs = oldOptionalMonotonicityInfo.eInverseRemove(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__OPTIONAL_MONOTONICITY_INFO, null, null);
				if (newOptionalMonotonicityInfo.eInternalContainer() == null)
				{
					msgs = newOptionalMonotonicityInfo.eInverseAdd(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__OPTIONAL_MONOTONICITY_INFO, null, msgs);
				}
				if (msgs != null) msgs.dispatch();
				if (eNotificationRequired())
					eNotify(new ENotificationImpl(this, Notification.RESOLVE, RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__OPTIONAL_MONOTONICITY_INFO, oldOptionalMonotonicityInfo, optionalMonotonicityInfo));
			}
		}
		return optionalMonotonicityInfo;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public MonotonicityInfo basicGetOptionalMonotonicityInfo()
	{
		return optionalMonotonicityInfo;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetOptionalMonotonicityInfo(MonotonicityInfo newOptionalMonotonicityInfo, NotificationChain msgs)
	{
		MonotonicityInfo oldOptionalMonotonicityInfo = optionalMonotonicityInfo;
		optionalMonotonicityInfo = newOptionalMonotonicityInfo;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__OPTIONAL_MONOTONICITY_INFO, oldOptionalMonotonicityInfo, newOptionalMonotonicityInfo);
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
	public void setOptionalMonotonicityInfo(MonotonicityInfo newOptionalMonotonicityInfo)
	{
		if (newOptionalMonotonicityInfo != optionalMonotonicityInfo)
		{
			NotificationChain msgs = null;
			if (optionalMonotonicityInfo != null)
				msgs = ((InternalEObject)optionalMonotonicityInfo).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__OPTIONAL_MONOTONICITY_INFO, null, msgs);
			if (newOptionalMonotonicityInfo != null)
				msgs = ((InternalEObject)newOptionalMonotonicityInfo).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__OPTIONAL_MONOTONICITY_INFO, null, msgs);
			msgs = basicSetOptionalMonotonicityInfo(newOptionalMonotonicityInfo, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__OPTIONAL_MONOTONICITY_INFO, newOptionalMonotonicityInfo, newOptionalMonotonicityInfo));
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
			case RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__OPTIONAL_MONOTONICITY_INFO:
				return basicSetOptionalMonotonicityInfo(null, msgs);
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
			case RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__DELETE_REDERIVE_EVALUATION:
				return isDeleteRederiveEvaluation();
			case RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__OPTIONAL_MONOTONICITY_INFO:
				if (resolve) return getOptionalMonotonicityInfo();
				return basicGetOptionalMonotonicityInfo();
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
			case RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__DELETE_REDERIVE_EVALUATION:
				setDeleteRederiveEvaluation((Boolean)newValue);
				return;
			case RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__OPTIONAL_MONOTONICITY_INFO:
				setOptionalMonotonicityInfo((MonotonicityInfo)newValue);
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
			case RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__DELETE_REDERIVE_EVALUATION:
				setDeleteRederiveEvaluation(DELETE_REDERIVE_EVALUATION_EDEFAULT);
				return;
			case RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__OPTIONAL_MONOTONICITY_INFO:
				setOptionalMonotonicityInfo((MonotonicityInfo)null);
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
			case RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__DELETE_REDERIVE_EVALUATION:
				return deleteRederiveEvaluation != DELETE_REDERIVE_EVALUATION_EDEFAULT;
			case RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__OPTIONAL_MONOTONICITY_INFO:
				return optionalMonotonicityInfo != null;
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
		if (baseClass == RederivableNodeRecipe.class)
		{
			switch (derivedFeatureID)
			{
				case RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__DELETE_REDERIVE_EVALUATION: return RecipesPackage.REDERIVABLE_NODE_RECIPE__DELETE_REDERIVE_EVALUATION;
				case RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__OPTIONAL_MONOTONICITY_INFO: return RecipesPackage.REDERIVABLE_NODE_RECIPE__OPTIONAL_MONOTONICITY_INFO;
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
		if (baseClass == RederivableNodeRecipe.class)
		{
			switch (baseFeatureID)
			{
				case RecipesPackage.REDERIVABLE_NODE_RECIPE__DELETE_REDERIVE_EVALUATION: return RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__DELETE_REDERIVE_EVALUATION;
				case RecipesPackage.REDERIVABLE_NODE_RECIPE__OPTIONAL_MONOTONICITY_INFO: return RecipesPackage.UNIQUENESS_ENFORCER_RECIPE__OPTIONAL_MONOTONICITY_INFO;
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
		result.append(" (deleteRederiveEvaluation: "); //$NON-NLS-1$
		result.append(deleteRederiveEvaluation);
		result.append(')');
		return result.toString();
	}

} //UniquenessEnforcerRecipeImpl
