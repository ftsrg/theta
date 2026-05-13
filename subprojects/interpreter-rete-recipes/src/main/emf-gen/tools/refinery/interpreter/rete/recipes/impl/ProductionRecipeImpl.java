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
import org.eclipse.emf.common.util.EMap;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import org.eclipse.emf.ecore.util.EcoreEMap;
import org.eclipse.emf.ecore.util.InternalEList;

import tools.refinery.interpreter.rete.recipes.MonotonicityInfo;
import tools.refinery.interpreter.rete.recipes.MultiParentNodeRecipe;
import tools.refinery.interpreter.rete.recipes.ProductionRecipe;
import tools.refinery.interpreter.rete.recipes.RecipesPackage;
import tools.refinery.interpreter.rete.recipes.RederivableNodeRecipe;
import tools.refinery.interpreter.rete.recipes.ReteNodeRecipe;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Production Recipe</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.ProductionRecipeImpl#isDeleteRederiveEvaluation <em>Delete Rederive Evaluation</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.ProductionRecipeImpl#getOptionalMonotonicityInfo <em>Optional Monotonicity Info</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.ProductionRecipeImpl#getMappedIndices <em>Mapped Indices</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.ProductionRecipeImpl#getPattern <em>Pattern</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.ProductionRecipeImpl#getPatternFQN <em>Pattern FQN</em>}</li>
 * </ul>
 *
 * @generated
 */
public class ProductionRecipeImpl extends MultiParentNodeRecipeImpl implements ProductionRecipe
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
	 * The cached value of the '{@link #getMappedIndices() <em>Mapped Indices</em>}' map.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getMappedIndices()
	 * @generated
	 * @ordered
	 */
	protected EMap<String, Integer> mappedIndices;

	/**
	 * The default value of the '{@link #getPattern() <em>Pattern</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getPattern()
	 * @generated
	 * @ordered
	 */
	protected static final Object PATTERN_EDEFAULT = null;

	/**
	 * The cached value of the '{@link #getPattern() <em>Pattern</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getPattern()
	 * @generated
	 * @ordered
	 */
	protected Object pattern = PATTERN_EDEFAULT;

	/**
	 * The default value of the '{@link #getPatternFQN() <em>Pattern FQN</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getPatternFQN()
	 * @generated
	 * @ordered
	 */
	protected static final String PATTERN_FQN_EDEFAULT = null;

	/**
	 * The cached value of the '{@link #getPatternFQN() <em>Pattern FQN</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getPatternFQN()
	 * @generated
	 * @ordered
	 */
	protected String patternFQN = PATTERN_FQN_EDEFAULT;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected ProductionRecipeImpl()
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
		return RecipesPackage.Literals.PRODUCTION_RECIPE;
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
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.PRODUCTION_RECIPE__DELETE_REDERIVE_EVALUATION, oldDeleteRederiveEvaluation, deleteRederiveEvaluation));
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
				NotificationChain msgs = oldOptionalMonotonicityInfo.eInverseRemove(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.PRODUCTION_RECIPE__OPTIONAL_MONOTONICITY_INFO, null, null);
				if (newOptionalMonotonicityInfo.eInternalContainer() == null)
				{
					msgs = newOptionalMonotonicityInfo.eInverseAdd(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.PRODUCTION_RECIPE__OPTIONAL_MONOTONICITY_INFO, null, msgs);
				}
				if (msgs != null) msgs.dispatch();
				if (eNotificationRequired())
					eNotify(new ENotificationImpl(this, Notification.RESOLVE, RecipesPackage.PRODUCTION_RECIPE__OPTIONAL_MONOTONICITY_INFO, oldOptionalMonotonicityInfo, optionalMonotonicityInfo));
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
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, RecipesPackage.PRODUCTION_RECIPE__OPTIONAL_MONOTONICITY_INFO, oldOptionalMonotonicityInfo, newOptionalMonotonicityInfo);
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
				msgs = ((InternalEObject)optionalMonotonicityInfo).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.PRODUCTION_RECIPE__OPTIONAL_MONOTONICITY_INFO, null, msgs);
			if (newOptionalMonotonicityInfo != null)
				msgs = ((InternalEObject)newOptionalMonotonicityInfo).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.PRODUCTION_RECIPE__OPTIONAL_MONOTONICITY_INFO, null, msgs);
			msgs = basicSetOptionalMonotonicityInfo(newOptionalMonotonicityInfo, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.PRODUCTION_RECIPE__OPTIONAL_MONOTONICITY_INFO, newOptionalMonotonicityInfo, newOptionalMonotonicityInfo));
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
			mappedIndices = new EcoreEMap<String,Integer>(RecipesPackage.Literals.STRING_INDEX_MAP_ENTRY, StringIndexMapEntryImpl.class, this, RecipesPackage.PRODUCTION_RECIPE__MAPPED_INDICES);
		}
		return mappedIndices;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object getPattern()
	{
		return pattern;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setPattern(Object newPattern)
	{
		Object oldPattern = pattern;
		pattern = newPattern;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.PRODUCTION_RECIPE__PATTERN, oldPattern, pattern));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public String getPatternFQN()
	{
		return patternFQN;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setPatternFQN(String newPatternFQN)
	{
		String oldPatternFQN = patternFQN;
		patternFQN = newPatternFQN;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.PRODUCTION_RECIPE__PATTERN_FQN, oldPatternFQN, patternFQN));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public int getArity()
	{
		return this.getMappedIndices().size();
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
			case RecipesPackage.PRODUCTION_RECIPE__OPTIONAL_MONOTONICITY_INFO:
				return basicSetOptionalMonotonicityInfo(null, msgs);
			case RecipesPackage.PRODUCTION_RECIPE__MAPPED_INDICES:
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
			case RecipesPackage.PRODUCTION_RECIPE__DELETE_REDERIVE_EVALUATION:
				return isDeleteRederiveEvaluation();
			case RecipesPackage.PRODUCTION_RECIPE__OPTIONAL_MONOTONICITY_INFO:
				if (resolve) return getOptionalMonotonicityInfo();
				return basicGetOptionalMonotonicityInfo();
			case RecipesPackage.PRODUCTION_RECIPE__MAPPED_INDICES:
				if (coreType) return getMappedIndices();
				else return getMappedIndices().map();
			case RecipesPackage.PRODUCTION_RECIPE__PATTERN:
				return getPattern();
			case RecipesPackage.PRODUCTION_RECIPE__PATTERN_FQN:
				return getPatternFQN();
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
			case RecipesPackage.PRODUCTION_RECIPE__DELETE_REDERIVE_EVALUATION:
				setDeleteRederiveEvaluation((Boolean)newValue);
				return;
			case RecipesPackage.PRODUCTION_RECIPE__OPTIONAL_MONOTONICITY_INFO:
				setOptionalMonotonicityInfo((MonotonicityInfo)newValue);
				return;
			case RecipesPackage.PRODUCTION_RECIPE__MAPPED_INDICES:
				((EStructuralFeature.Setting)getMappedIndices()).set(newValue);
				return;
			case RecipesPackage.PRODUCTION_RECIPE__PATTERN:
				setPattern(newValue);
				return;
			case RecipesPackage.PRODUCTION_RECIPE__PATTERN_FQN:
				setPatternFQN((String)newValue);
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
			case RecipesPackage.PRODUCTION_RECIPE__DELETE_REDERIVE_EVALUATION:
				setDeleteRederiveEvaluation(DELETE_REDERIVE_EVALUATION_EDEFAULT);
				return;
			case RecipesPackage.PRODUCTION_RECIPE__OPTIONAL_MONOTONICITY_INFO:
				setOptionalMonotonicityInfo((MonotonicityInfo)null);
				return;
			case RecipesPackage.PRODUCTION_RECIPE__MAPPED_INDICES:
				getMappedIndices().clear();
				return;
			case RecipesPackage.PRODUCTION_RECIPE__PATTERN:
				setPattern(PATTERN_EDEFAULT);
				return;
			case RecipesPackage.PRODUCTION_RECIPE__PATTERN_FQN:
				setPatternFQN(PATTERN_FQN_EDEFAULT);
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
			case RecipesPackage.PRODUCTION_RECIPE__DELETE_REDERIVE_EVALUATION:
				return deleteRederiveEvaluation != DELETE_REDERIVE_EVALUATION_EDEFAULT;
			case RecipesPackage.PRODUCTION_RECIPE__OPTIONAL_MONOTONICITY_INFO:
				return optionalMonotonicityInfo != null;
			case RecipesPackage.PRODUCTION_RECIPE__MAPPED_INDICES:
				return mappedIndices != null && !mappedIndices.isEmpty();
			case RecipesPackage.PRODUCTION_RECIPE__PATTERN:
				return PATTERN_EDEFAULT == null ? pattern != null : !PATTERN_EDEFAULT.equals(pattern);
			case RecipesPackage.PRODUCTION_RECIPE__PATTERN_FQN:
				return PATTERN_FQN_EDEFAULT == null ? patternFQN != null : !PATTERN_FQN_EDEFAULT.equals(patternFQN);
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
				case RecipesPackage.PRODUCTION_RECIPE__DELETE_REDERIVE_EVALUATION: return RecipesPackage.REDERIVABLE_NODE_RECIPE__DELETE_REDERIVE_EVALUATION;
				case RecipesPackage.PRODUCTION_RECIPE__OPTIONAL_MONOTONICITY_INFO: return RecipesPackage.REDERIVABLE_NODE_RECIPE__OPTIONAL_MONOTONICITY_INFO;
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
				case RecipesPackage.REDERIVABLE_NODE_RECIPE__DELETE_REDERIVE_EVALUATION: return RecipesPackage.PRODUCTION_RECIPE__DELETE_REDERIVE_EVALUATION;
				case RecipesPackage.REDERIVABLE_NODE_RECIPE__OPTIONAL_MONOTONICITY_INFO: return RecipesPackage.PRODUCTION_RECIPE__OPTIONAL_MONOTONICITY_INFO;
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
	public int eDerivedOperationID(int baseOperationID, Class<?> baseClass)
	{
		if (baseClass == ReteNodeRecipe.class)
		{
			switch (baseOperationID)
			{
				case RecipesPackage.RETE_NODE_RECIPE___GET_ARITY: return RecipesPackage.PRODUCTION_RECIPE___GET_ARITY;
				default: return super.eDerivedOperationID(baseOperationID, baseClass);
			}
		}
		if (baseClass == MultiParentNodeRecipe.class)
		{
			switch (baseOperationID)
			{
				case RecipesPackage.MULTI_PARENT_NODE_RECIPE___GET_ARITY: return RecipesPackage.PRODUCTION_RECIPE___GET_ARITY;
				default: return super.eDerivedOperationID(baseOperationID, baseClass);
			}
		}
		if (baseClass == RederivableNodeRecipe.class)
		{
			switch (baseOperationID)
			{
				default: return -1;
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
			case RecipesPackage.PRODUCTION_RECIPE___GET_ARITY:
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
		result.append(" (deleteRederiveEvaluation: "); //$NON-NLS-1$
		result.append(deleteRederiveEvaluation);
		result.append(", pattern: "); //$NON-NLS-1$
		result.append(pattern);
		result.append(", patternFQN: "); //$NON-NLS-1$
		result.append(patternFQN);
		result.append(')');
		return result.toString();
	}

} //ProductionRecipeImpl
