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

import tools.refinery.interpreter.rete.recipes.BetaRecipe;
import tools.refinery.interpreter.rete.recipes.IndexerRecipe;
import tools.refinery.interpreter.rete.recipes.ProjectionIndexerRecipe;
import tools.refinery.interpreter.rete.recipes.RecipesPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Beta Recipe</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.BetaRecipeImpl#getLeftParent <em>Left Parent</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.BetaRecipeImpl#getRightParent <em>Right Parent</em>}</li>
 * </ul>
 *
 * @generated
 */
public abstract class BetaRecipeImpl extends ReteNodeRecipeImpl implements BetaRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static final String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * The cached value of the '{@link #getLeftParent() <em>Left Parent</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getLeftParent()
	 * @generated
	 * @ordered
	 */
	protected ProjectionIndexerRecipe leftParent;

	/**
	 * The cached value of the '{@link #getRightParent() <em>Right Parent</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getRightParent()
	 * @generated
	 * @ordered
	 */
	protected IndexerRecipe rightParent;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected BetaRecipeImpl()
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
		return RecipesPackage.Literals.BETA_RECIPE;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public ProjectionIndexerRecipe getLeftParent()
	{
		return leftParent;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetLeftParent(ProjectionIndexerRecipe newLeftParent, NotificationChain msgs)
	{
		ProjectionIndexerRecipe oldLeftParent = leftParent;
		leftParent = newLeftParent;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, RecipesPackage.BETA_RECIPE__LEFT_PARENT, oldLeftParent, newLeftParent);
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
	public void setLeftParent(ProjectionIndexerRecipe newLeftParent)
	{
		if (newLeftParent != leftParent)
		{
			NotificationChain msgs = null;
			if (leftParent != null)
				msgs = ((InternalEObject)leftParent).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.BETA_RECIPE__LEFT_PARENT, null, msgs);
			if (newLeftParent != null)
				msgs = ((InternalEObject)newLeftParent).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.BETA_RECIPE__LEFT_PARENT, null, msgs);
			msgs = basicSetLeftParent(newLeftParent, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.BETA_RECIPE__LEFT_PARENT, newLeftParent, newLeftParent));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public IndexerRecipe getRightParent()
	{
		return rightParent;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetRightParent(IndexerRecipe newRightParent, NotificationChain msgs)
	{
		IndexerRecipe oldRightParent = rightParent;
		rightParent = newRightParent;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, RecipesPackage.BETA_RECIPE__RIGHT_PARENT, oldRightParent, newRightParent);
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
	public void setRightParent(IndexerRecipe newRightParent)
	{
		if (newRightParent != rightParent)
		{
			NotificationChain msgs = null;
			if (rightParent != null)
				msgs = ((InternalEObject)rightParent).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.BETA_RECIPE__RIGHT_PARENT, null, msgs);
			if (newRightParent != null)
				msgs = ((InternalEObject)newRightParent).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - RecipesPackage.BETA_RECIPE__RIGHT_PARENT, null, msgs);
			msgs = basicSetRightParent(newRightParent, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.BETA_RECIPE__RIGHT_PARENT, newRightParent, newRightParent));
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
			case RecipesPackage.BETA_RECIPE__LEFT_PARENT:
				return basicSetLeftParent(null, msgs);
			case RecipesPackage.BETA_RECIPE__RIGHT_PARENT:
				return basicSetRightParent(null, msgs);
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
			case RecipesPackage.BETA_RECIPE__LEFT_PARENT:
				return getLeftParent();
			case RecipesPackage.BETA_RECIPE__RIGHT_PARENT:
				return getRightParent();
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
			case RecipesPackage.BETA_RECIPE__LEFT_PARENT:
				setLeftParent((ProjectionIndexerRecipe)newValue);
				return;
			case RecipesPackage.BETA_RECIPE__RIGHT_PARENT:
				setRightParent((IndexerRecipe)newValue);
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
			case RecipesPackage.BETA_RECIPE__LEFT_PARENT:
				setLeftParent((ProjectionIndexerRecipe)null);
				return;
			case RecipesPackage.BETA_RECIPE__RIGHT_PARENT:
				setRightParent((IndexerRecipe)null);
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
			case RecipesPackage.BETA_RECIPE__LEFT_PARENT:
				return leftParent != null;
			case RecipesPackage.BETA_RECIPE__RIGHT_PARENT:
				return rightParent != null;
		}
		return super.eIsSet(featureID);
	}

} //BetaRecipeImpl
