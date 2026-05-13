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

import tools.refinery.interpreter.matchers.psystem.aggregations.IMultisetAggregationOperator;

import tools.refinery.interpreter.rete.recipes.Mask;
import tools.refinery.interpreter.rete.recipes.MonotonicityInfo;
import tools.refinery.interpreter.rete.recipes.RecipesPackage;
import tools.refinery.interpreter.rete.recipes.RederivableNodeRecipe;
import tools.refinery.interpreter.rete.recipes.ReteNodeRecipe;
import tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Single Column Aggregator Recipe</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.SingleColumnAggregatorRecipeImpl#isDeleteRederiveEvaluation <em>Delete Rederive Evaluation</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.SingleColumnAggregatorRecipeImpl#getOptionalMonotonicityInfo <em>Optional Monotonicity Info</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.SingleColumnAggregatorRecipeImpl#getMultisetAggregationOperator <em>Multiset Aggregation Operator</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.SingleColumnAggregatorRecipeImpl#getAggregableIndex <em>Aggregable Index</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.SingleColumnAggregatorRecipeImpl#getGroupByMask <em>Group By Mask</em>}</li>
 * </ul>
 *
 * @generated
 */
public class SingleColumnAggregatorRecipeImpl extends AlphaRecipeImpl implements SingleColumnAggregatorRecipe
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
	 * The cached value of the '{@link #getMultisetAggregationOperator() <em>Multiset Aggregation Operator</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getMultisetAggregationOperator()
	 * @generated
	 * @ordered
	 */
	protected IMultisetAggregationOperator<?, ?, ?> multisetAggregationOperator;

	/**
	 * The default value of the '{@link #getAggregableIndex() <em>Aggregable Index</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getAggregableIndex()
	 * @generated
	 * @ordered
	 */
	protected static final int AGGREGABLE_INDEX_EDEFAULT = 0;

	/**
	 * The cached value of the '{@link #getAggregableIndex() <em>Aggregable Index</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getAggregableIndex()
	 * @generated
	 * @ordered
	 */
	protected int aggregableIndex = AGGREGABLE_INDEX_EDEFAULT;

	/**
	 * The cached value of the '{@link #getGroupByMask() <em>Group By Mask</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getGroupByMask()
	 * @generated
	 * @ordered
	 */
	protected Mask groupByMask;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected SingleColumnAggregatorRecipeImpl()
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
		return RecipesPackage.Literals.SINGLE_COLUMN_AGGREGATOR_RECIPE;
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
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__DELETE_REDERIVE_EVALUATION, oldDeleteRederiveEvaluation, deleteRederiveEvaluation));
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
				NotificationChain msgs = oldOptionalMonotonicityInfo.eInverseRemove(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__OPTIONAL_MONOTONICITY_INFO, null, null);
				if (newOptionalMonotonicityInfo.eInternalContainer() == null)
				{
					msgs = newOptionalMonotonicityInfo.eInverseAdd(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__OPTIONAL_MONOTONICITY_INFO, null, msgs);
				}
				if (msgs != null) msgs.dispatch();
				if (eNotificationRequired())
					eNotify(new ENotificationImpl(this, Notification.RESOLVE, RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__OPTIONAL_MONOTONICITY_INFO, oldOptionalMonotonicityInfo, optionalMonotonicityInfo));
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
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__OPTIONAL_MONOTONICITY_INFO, oldOptionalMonotonicityInfo, newOptionalMonotonicityInfo);
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
				msgs = ((InternalEObject)optionalMonotonicityInfo).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__OPTIONAL_MONOTONICITY_INFO, null, msgs);
			if (newOptionalMonotonicityInfo != null)
				msgs = ((InternalEObject)newOptionalMonotonicityInfo).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__OPTIONAL_MONOTONICITY_INFO, null, msgs);
			msgs = basicSetOptionalMonotonicityInfo(newOptionalMonotonicityInfo, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__OPTIONAL_MONOTONICITY_INFO, newOptionalMonotonicityInfo, newOptionalMonotonicityInfo));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public IMultisetAggregationOperator<?, ?, ?> getMultisetAggregationOperator()
	{
		return multisetAggregationOperator;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setMultisetAggregationOperator(IMultisetAggregationOperator<?, ?, ?> newMultisetAggregationOperator)
	{
		IMultisetAggregationOperator<?, ?, ?> oldMultisetAggregationOperator = multisetAggregationOperator;
		multisetAggregationOperator = newMultisetAggregationOperator;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__MULTISET_AGGREGATION_OPERATOR, oldMultisetAggregationOperator, multisetAggregationOperator));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public int getAggregableIndex()
	{
		return aggregableIndex;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setAggregableIndex(int newAggregableIndex)
	{
		int oldAggregableIndex = aggregableIndex;
		aggregableIndex = newAggregableIndex;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__AGGREGABLE_INDEX, oldAggregableIndex, aggregableIndex));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Mask getGroupByMask()
	{
		if (groupByMask != null && groupByMask.eIsProxy())
		{
			InternalEObject oldGroupByMask = (InternalEObject)groupByMask;
			groupByMask = (Mask)eResolveProxy(oldGroupByMask);
			if (groupByMask != oldGroupByMask)
			{
				InternalEObject newGroupByMask = (InternalEObject)groupByMask;
				NotificationChain msgs = oldGroupByMask.eInverseRemove(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__GROUP_BY_MASK, null, null);
				if (newGroupByMask.eInternalContainer() == null)
				{
					msgs = newGroupByMask.eInverseAdd(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__GROUP_BY_MASK, null, msgs);
				}
				if (msgs != null) msgs.dispatch();
				if (eNotificationRequired())
					eNotify(new ENotificationImpl(this, Notification.RESOLVE, RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__GROUP_BY_MASK, oldGroupByMask, groupByMask));
			}
		}
		return groupByMask;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Mask basicGetGroupByMask()
	{
		return groupByMask;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetGroupByMask(Mask newGroupByMask, NotificationChain msgs)
	{
		Mask oldGroupByMask = groupByMask;
		groupByMask = newGroupByMask;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__GROUP_BY_MASK, oldGroupByMask, newGroupByMask);
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
	public void setGroupByMask(Mask newGroupByMask)
	{
		if (newGroupByMask != groupByMask)
		{
			NotificationChain msgs = null;
			if (groupByMask != null)
				msgs = ((InternalEObject)groupByMask).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__GROUP_BY_MASK, null, msgs);
			if (newGroupByMask != null)
				msgs = ((InternalEObject)newGroupByMask).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__GROUP_BY_MASK, null, msgs);
			msgs = basicSetGroupByMask(newGroupByMask, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__GROUP_BY_MASK, newGroupByMask, newGroupByMask));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public int getArity()
	{
		MonotonicityInfo info = getOptionalMonotonicityInfo();
		if (info == null) {
			return 1 + getGroupByMask().getSourceIndices().size();
		} else {	
			return info.getCoreMask().getSourceIndices().size() + info.getPosetMask().getSourceIndices().size();
		}
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
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__OPTIONAL_MONOTONICITY_INFO:
				return basicSetOptionalMonotonicityInfo(null, msgs);
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__GROUP_BY_MASK:
				return basicSetGroupByMask(null, msgs);
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
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__DELETE_REDERIVE_EVALUATION:
				return isDeleteRederiveEvaluation();
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__OPTIONAL_MONOTONICITY_INFO:
				if (resolve) return getOptionalMonotonicityInfo();
				return basicGetOptionalMonotonicityInfo();
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__MULTISET_AGGREGATION_OPERATOR:
				return getMultisetAggregationOperator();
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__AGGREGABLE_INDEX:
				return getAggregableIndex();
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__GROUP_BY_MASK:
				if (resolve) return getGroupByMask();
				return basicGetGroupByMask();
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
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__DELETE_REDERIVE_EVALUATION:
				setDeleteRederiveEvaluation((Boolean)newValue);
				return;
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__OPTIONAL_MONOTONICITY_INFO:
				setOptionalMonotonicityInfo((MonotonicityInfo)newValue);
				return;
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__MULTISET_AGGREGATION_OPERATOR:
				setMultisetAggregationOperator((IMultisetAggregationOperator<?, ?, ?>)newValue);
				return;
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__AGGREGABLE_INDEX:
				setAggregableIndex((Integer)newValue);
				return;
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__GROUP_BY_MASK:
				setGroupByMask((Mask)newValue);
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
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__DELETE_REDERIVE_EVALUATION:
				setDeleteRederiveEvaluation(DELETE_REDERIVE_EVALUATION_EDEFAULT);
				return;
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__OPTIONAL_MONOTONICITY_INFO:
				setOptionalMonotonicityInfo((MonotonicityInfo)null);
				return;
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__MULTISET_AGGREGATION_OPERATOR:
				setMultisetAggregationOperator((IMultisetAggregationOperator<?, ?, ?>)null);
				return;
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__AGGREGABLE_INDEX:
				setAggregableIndex(AGGREGABLE_INDEX_EDEFAULT);
				return;
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__GROUP_BY_MASK:
				setGroupByMask((Mask)null);
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
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__DELETE_REDERIVE_EVALUATION:
				return deleteRederiveEvaluation != DELETE_REDERIVE_EVALUATION_EDEFAULT;
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__OPTIONAL_MONOTONICITY_INFO:
				return optionalMonotonicityInfo != null;
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__MULTISET_AGGREGATION_OPERATOR:
				return multisetAggregationOperator != null;
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__AGGREGABLE_INDEX:
				return aggregableIndex != AGGREGABLE_INDEX_EDEFAULT;
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__GROUP_BY_MASK:
				return groupByMask != null;
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
				case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__DELETE_REDERIVE_EVALUATION: return RecipesPackage.REDERIVABLE_NODE_RECIPE__DELETE_REDERIVE_EVALUATION;
				case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__OPTIONAL_MONOTONICITY_INFO: return RecipesPackage.REDERIVABLE_NODE_RECIPE__OPTIONAL_MONOTONICITY_INFO;
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
				case RecipesPackage.REDERIVABLE_NODE_RECIPE__DELETE_REDERIVE_EVALUATION: return RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__DELETE_REDERIVE_EVALUATION;
				case RecipesPackage.REDERIVABLE_NODE_RECIPE__OPTIONAL_MONOTONICITY_INFO: return RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE__OPTIONAL_MONOTONICITY_INFO;
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
				case RecipesPackage.RETE_NODE_RECIPE___GET_ARITY: return RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE___GET_ARITY;
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
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE___GET_ARITY:
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
		result.append(", multisetAggregationOperator: "); //$NON-NLS-1$
		result.append(multisetAggregationOperator);
		result.append(", aggregableIndex: "); //$NON-NLS-1$
		result.append(aggregableIndex);
		result.append(')');
		return result.toString();
	}

} //SingleColumnAggregatorRecipeImpl
