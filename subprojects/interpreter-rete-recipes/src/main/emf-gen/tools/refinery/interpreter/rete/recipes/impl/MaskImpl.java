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

import java.util.Collection;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

import org.eclipse.emf.ecore.util.EDataTypeEList;

import tools.refinery.interpreter.rete.recipes.Mask;
import tools.refinery.interpreter.rete.recipes.RecipesPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Mask</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.MaskImpl#getSourceIndices <em>Source Indices</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.impl.MaskImpl#getSourceArity <em>Source Arity</em>}</li>
 * </ul>
 *
 * @generated
 */
public class MaskImpl extends MinimalEObjectImpl.Container implements Mask
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static final String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * The cached value of the '{@link #getSourceIndices() <em>Source Indices</em>}' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getSourceIndices()
	 * @generated
	 * @ordered
	 */
	protected EList<Integer> sourceIndices;

	/**
	 * The default value of the '{@link #getSourceArity() <em>Source Arity</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getSourceArity()
	 * @generated
	 * @ordered
	 */
	protected static final int SOURCE_ARITY_EDEFAULT = 0;

	/**
	 * The cached value of the '{@link #getSourceArity() <em>Source Arity</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getSourceArity()
	 * @generated
	 * @ordered
	 */
	protected int sourceArity = SOURCE_ARITY_EDEFAULT;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected MaskImpl()
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
		return RecipesPackage.Literals.MASK;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EList<Integer> getSourceIndices()
	{
		if (sourceIndices == null)
		{
			sourceIndices = new EDataTypeEList<Integer>(Integer.class, this, RecipesPackage.MASK__SOURCE_INDICES);
		}
		return sourceIndices;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public int getSourceArity()
	{
		return sourceArity;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void setSourceArity(int newSourceArity)
	{
		int oldSourceArity = sourceArity;
		sourceArity = newSourceArity;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, RecipesPackage.MASK__SOURCE_ARITY, oldSourceArity, sourceArity));
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
			case RecipesPackage.MASK__SOURCE_INDICES:
				return getSourceIndices();
			case RecipesPackage.MASK__SOURCE_ARITY:
				return getSourceArity();
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
			case RecipesPackage.MASK__SOURCE_INDICES:
				getSourceIndices().clear();
				getSourceIndices().addAll((Collection<? extends Integer>)newValue);
				return;
			case RecipesPackage.MASK__SOURCE_ARITY:
				setSourceArity((Integer)newValue);
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
			case RecipesPackage.MASK__SOURCE_INDICES:
				getSourceIndices().clear();
				return;
			case RecipesPackage.MASK__SOURCE_ARITY:
				setSourceArity(SOURCE_ARITY_EDEFAULT);
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
			case RecipesPackage.MASK__SOURCE_INDICES:
				return sourceIndices != null && !sourceIndices.isEmpty();
			case RecipesPackage.MASK__SOURCE_ARITY:
				return sourceArity != SOURCE_ARITY_EDEFAULT;
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
		result.append(" (sourceIndices: "); //$NON-NLS-1$
		result.append(sourceIndices);
		result.append(", sourceArity: "); //$NON-NLS-1$
		result.append(sourceArity);
		result.append(')');
		return result.toString();
	}

} //MaskImpl
