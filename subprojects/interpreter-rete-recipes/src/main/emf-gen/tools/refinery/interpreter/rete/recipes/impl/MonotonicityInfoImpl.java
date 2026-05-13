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
import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

import tools.refinery.interpreter.rete.recipes.Mask;
import tools.refinery.interpreter.rete.recipes.MonotonicityInfo;
import tools.refinery.interpreter.rete.recipes.RecipesPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Monotonicity Info</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.MonotonicityInfoImpl#getCoreMask <em>Core Mask</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.MonotonicityInfoImpl#getPosetMask <em>Poset Mask</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.MonotonicityInfoImpl#getPosetComparator <em>Poset Comparator</em>}</li>
 * </ul>
 *
 * @generated
 */
public class MonotonicityInfoImpl extends MinimalEObjectImpl.Container implements MonotonicityInfo
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static final String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * The cached value of the '{@link #getCoreMask() <em>Core Mask</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getCoreMask()
	 * @generated
	 * @ordered
	 */
	protected Mask coreMask;

	/**
	 * The cached value of the '{@link #getPosetMask() <em>Poset Mask</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getPosetMask()
	 * @generated
	 * @ordered
	 */
	protected Mask posetMask;

	/**
	 * The default value of the '{@link #getPosetComparator() <em>Poset Comparator</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getPosetComparator()
	 * @generated
	 * @ordered
	 */
	protected static final Object POSET_COMPARATOR_EDEFAULT = null;

	/**
	 * The cached value of the '{@link #getPosetComparator() <em>Poset Comparator</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getPosetComparator()
	 * @generated
	 * @ordered
	 */
	protected Object posetComparator = POSET_COMPARATOR_EDEFAULT;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected MonotonicityInfoImpl()
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
		return RecipesPackage.Literals.MONOTONICITY_INFO;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Mask getCoreMask()
	{
		return coreMask;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetCoreMask(Mask newCoreMask, NotificationChain msgs)
	{
		Mask oldCoreMask = coreMask;
		coreMask = newCoreMask;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, RecipesPackage.MONOTONICITY_INFO__CORE_MASK, oldCoreMask, newCoreMask);
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
	public void setCoreMask(Mask newCoreMask)
	{
		if (newCoreMask != coreMask)
		{
			NotificationChain msgs = null;
			if (coreMask != null)
				msgs = ((InternalEObject)coreMask).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.MONOTONICITY_INFO__CORE_MASK, null, msgs);
			if (newCoreMask != null)
				msgs = ((InternalEObject)newCoreMask).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.MONOTONICITY_INFO__CORE_MASK, null, msgs);
			msgs = basicSetCoreMask(newCoreMask, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.MONOTONICITY_INFO__CORE_MASK, newCoreMask, newCoreMask));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Mask getPosetMask()
	{
		return posetMask;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetPosetMask(Mask newPosetMask, NotificationChain msgs)
	{
		Mask oldPosetMask = posetMask;
		posetMask = newPosetMask;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, RecipesPackage.MONOTONICITY_INFO__POSET_MASK, oldPosetMask, newPosetMask);
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
	public void setPosetMask(Mask newPosetMask)
	{
		if (newPosetMask != posetMask)
		{
			NotificationChain msgs = null;
			if (posetMask != null)
				msgs = ((InternalEObject)posetMask).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.MONOTONICITY_INFO__POSET_MASK, null, msgs);
			if (newPosetMask != null)
				msgs = ((InternalEObject)newPosetMask).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.MONOTONICITY_INFO__POSET_MASK, null, msgs);
			msgs = basicSetPosetMask(newPosetMask, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.MONOTONICITY_INFO__POSET_MASK, newPosetMask, newPosetMask));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object getPosetComparator()
	{
		return posetComparator;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setPosetComparator(Object newPosetComparator)
	{
		Object oldPosetComparator = posetComparator;
		posetComparator = newPosetComparator;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.MONOTONICITY_INFO__POSET_COMPARATOR, oldPosetComparator, posetComparator));
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
			case RecipesPackage.MONOTONICITY_INFO__CORE_MASK:
				return basicSetCoreMask(null, msgs);
			case RecipesPackage.MONOTONICITY_INFO__POSET_MASK:
				return basicSetPosetMask(null, msgs);
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
			case RecipesPackage.MONOTONICITY_INFO__CORE_MASK:
				return getCoreMask();
			case RecipesPackage.MONOTONICITY_INFO__POSET_MASK:
				return getPosetMask();
			case RecipesPackage.MONOTONICITY_INFO__POSET_COMPARATOR:
				return getPosetComparator();
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
			case RecipesPackage.MONOTONICITY_INFO__CORE_MASK:
				setCoreMask((Mask)newValue);
				return;
			case RecipesPackage.MONOTONICITY_INFO__POSET_MASK:
				setPosetMask((Mask)newValue);
				return;
			case RecipesPackage.MONOTONICITY_INFO__POSET_COMPARATOR:
				setPosetComparator(newValue);
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
			case RecipesPackage.MONOTONICITY_INFO__CORE_MASK:
				setCoreMask((Mask)null);
				return;
			case RecipesPackage.MONOTONICITY_INFO__POSET_MASK:
				setPosetMask((Mask)null);
				return;
			case RecipesPackage.MONOTONICITY_INFO__POSET_COMPARATOR:
				setPosetComparator(POSET_COMPARATOR_EDEFAULT);
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
			case RecipesPackage.MONOTONICITY_INFO__CORE_MASK:
				return coreMask != null;
			case RecipesPackage.MONOTONICITY_INFO__POSET_MASK:
				return posetMask != null;
			case RecipesPackage.MONOTONICITY_INFO__POSET_COMPARATOR:
				return POSET_COMPARATOR_EDEFAULT == null ? posetComparator != null : !POSET_COMPARATOR_EDEFAULT.equals(posetComparator);
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
		result.append(" (posetComparator: "); //$NON-NLS-1$
		result.append(posetComparator);
		result.append(')');
		return result.toString();
	}

} //MonotonicityInfoImpl
