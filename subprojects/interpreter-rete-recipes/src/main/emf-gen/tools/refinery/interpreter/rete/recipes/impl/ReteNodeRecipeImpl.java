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

import java.util.Collection;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

import org.eclipse.emf.ecore.util.EDataTypeUniqueEList;

import tools.refinery.interpreter.rete.recipes.RecipesPackage;
import tools.refinery.interpreter.rete.recipes.ReteNodeRecipe;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Rete Node Recipe</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.ReteNodeRecipeImpl#getTraceInfo <em>Trace Info</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.ReteNodeRecipeImpl#getEquivalenceClassIDs <em>Equivalence Class IDs</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.ReteNodeRecipeImpl#getCachedHashCode <em>Cached Hash Code</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.ReteNodeRecipeImpl#isConstructed <em>Constructed</em>}</li>
 * </ul>
 *
 * @generated
 */
public abstract class ReteNodeRecipeImpl extends MinimalEObjectImpl.Container implements ReteNodeRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static final String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * The default value of the '{@link #getTraceInfo() <em>Trace Info</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getTraceInfo()
	 * @generated
	 * @ordered
	 */
	protected static final String TRACE_INFO_EDEFAULT = null;

	/**
	 * The cached value of the '{@link #getTraceInfo() <em>Trace Info</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getTraceInfo()
	 * @generated
	 * @ordered
	 */
	protected String traceInfo = TRACE_INFO_EDEFAULT;

	/**
	 * The cached value of the '{@link #getEquivalenceClassIDs() <em>Equivalence Class IDs</em>}' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getEquivalenceClassIDs()
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	protected EList<Long> equivalenceClassIDs;

	/**
	 * The default value of the '{@link #getCachedHashCode() <em>Cached Hash Code</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getCachedHashCode()
	 * @generated
	 * @ordered
	 */
	protected static final Long CACHED_HASH_CODE_EDEFAULT = null;

	/**
	 * The cached value of the '{@link #getCachedHashCode() <em>Cached Hash Code</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getCachedHashCode()
	 * @generated
	 * @ordered
	 */
	protected Long cachedHashCode = CACHED_HASH_CODE_EDEFAULT;

	/**
	 * The default value of the '{@link #isConstructed() <em>Constructed</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isConstructed()
	 * @generated
	 * @ordered
	 */
	protected static final boolean CONSTRUCTED_EDEFAULT = false;

	/**
	 * The cached value of the '{@link #isConstructed() <em>Constructed</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isConstructed()
	 * @generated
	 * @ordered
	 */
	protected boolean constructed = CONSTRUCTED_EDEFAULT;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected ReteNodeRecipeImpl()
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
		return RecipesPackage.Literals.RETE_NODE_RECIPE;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public String getTraceInfo()
	{
		return traceInfo;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setTraceInfo(String newTraceInfo)
	{
		String oldTraceInfo = traceInfo;
		traceInfo = newTraceInfo;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.RETE_NODE_RECIPE__TRACE_INFO, oldTraceInfo, traceInfo));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 */
	@Override
	public EList<Long> getEquivalenceClassIDs()
	{
		if (equivalenceClassIDs == null)
		{
			equivalenceClassIDs = new EDataTypeUniqueEList<Long>(Long.class, this, RecipesPackage.RETE_NODE_RECIPE__EQUIVALENCE_CLASS_IDS);
		}
		return equivalenceClassIDs;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Long getCachedHashCode()
	{
		return cachedHashCode;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setCachedHashCode(Long newCachedHashCode)
	{
		Long oldCachedHashCode = cachedHashCode;
		cachedHashCode = newCachedHashCode;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.RETE_NODE_RECIPE__CACHED_HASH_CODE, oldCachedHashCode, cachedHashCode));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public boolean isConstructed()
	{
		return constructed;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setConstructed(boolean newConstructed)
	{
		boolean oldConstructed = constructed;
		constructed = newConstructed;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.RETE_NODE_RECIPE__CONSTRUCTED, oldConstructed, constructed));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public int getArity()
	{
		throw new UnsupportedOperationException();
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
			case RecipesPackage.RETE_NODE_RECIPE__TRACE_INFO:
				return getTraceInfo();
			case RecipesPackage.RETE_NODE_RECIPE__EQUIVALENCE_CLASS_IDS:
				return getEquivalenceClassIDs();
			case RecipesPackage.RETE_NODE_RECIPE__CACHED_HASH_CODE:
				return getCachedHashCode();
			case RecipesPackage.RETE_NODE_RECIPE__CONSTRUCTED:
				return isConstructed();
		}
		return super.eGet(featureID, resolve, coreType);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@SuppressWarnings("unchecked")
	@Override
	public void eSet(int featureID, Object newValue)
	{
		switch (featureID)
		{
			case RecipesPackage.RETE_NODE_RECIPE__TRACE_INFO:
				setTraceInfo((String)newValue);
				return;
			case RecipesPackage.RETE_NODE_RECIPE__EQUIVALENCE_CLASS_IDS:
				getEquivalenceClassIDs().clear();
				getEquivalenceClassIDs().addAll((Collection<? extends Long>)newValue);
				return;
			case RecipesPackage.RETE_NODE_RECIPE__CACHED_HASH_CODE:
				setCachedHashCode((Long)newValue);
				return;
			case RecipesPackage.RETE_NODE_RECIPE__CONSTRUCTED:
				setConstructed((Boolean)newValue);
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
			case RecipesPackage.RETE_NODE_RECIPE__TRACE_INFO:
				setTraceInfo(TRACE_INFO_EDEFAULT);
				return;
			case RecipesPackage.RETE_NODE_RECIPE__EQUIVALENCE_CLASS_IDS:
				getEquivalenceClassIDs().clear();
				return;
			case RecipesPackage.RETE_NODE_RECIPE__CACHED_HASH_CODE:
				setCachedHashCode(CACHED_HASH_CODE_EDEFAULT);
				return;
			case RecipesPackage.RETE_NODE_RECIPE__CONSTRUCTED:
				setConstructed(CONSTRUCTED_EDEFAULT);
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
			case RecipesPackage.RETE_NODE_RECIPE__TRACE_INFO:
				return TRACE_INFO_EDEFAULT == null ? traceInfo != null : !TRACE_INFO_EDEFAULT.equals(traceInfo);
			case RecipesPackage.RETE_NODE_RECIPE__EQUIVALENCE_CLASS_IDS:
				return equivalenceClassIDs != null && !equivalenceClassIDs.isEmpty();
			case RecipesPackage.RETE_NODE_RECIPE__CACHED_HASH_CODE:
				return CACHED_HASH_CODE_EDEFAULT == null ? cachedHashCode != null : !CACHED_HASH_CODE_EDEFAULT.equals(cachedHashCode);
			case RecipesPackage.RETE_NODE_RECIPE__CONSTRUCTED:
				return constructed != CONSTRUCTED_EDEFAULT;
		}
		return super.eIsSet(featureID);
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
			case RecipesPackage.RETE_NODE_RECIPE___GET_ARITY:
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
		result.append(" (traceInfo: "); //$NON-NLS-1$
		result.append(traceInfo);
		result.append(", equivalenceClassIDs: "); //$NON-NLS-1$
		result.append(equivalenceClassIDs);
		result.append(", cachedHashCode: "); //$NON-NLS-1$
		result.append(cachedHashCode);
		result.append(", constructed: "); //$NON-NLS-1$
		result.append(constructed);
		result.append(')');
		return result.toString();
	}

} //ReteNodeRecipeImpl
