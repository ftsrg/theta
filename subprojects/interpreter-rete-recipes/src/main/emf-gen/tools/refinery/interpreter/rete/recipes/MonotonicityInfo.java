/**
 * Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro
 * Copyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License v. 2.0 which is available at
 * http://www.eclipse.org/legal/epl-v20.html.
 * 
 * SPDX-License-Identifier: EPL-2.0
 */
package tools.refinery.interpreter.rete.recipes;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Monotonicity Info</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.MonotonicityInfo#getCoreMask <em>Core Mask</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.MonotonicityInfo#getPosetMask <em>Poset Mask</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.MonotonicityInfo#getPosetComparator <em>Poset Comparator</em>}</li>
 * </ul>
 *
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getMonotonicityInfo()
 * @model
 * @generated
 */
public interface MonotonicityInfo extends EObject
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * Returns the value of the '<em><b>Core Mask</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Core Mask</em>' containment reference.
	 * @see #setCoreMask(Mask)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getMonotonicityInfo_CoreMask()
	 * @model containment="true"
	 * @generated
	 */
	Mask getCoreMask();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.MonotonicityInfo#getCoreMask <em>Core Mask</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Core Mask</em>' containment reference.
	 * @see #getCoreMask()
	 * @generated
	 */
	void setCoreMask(Mask value);

	/**
	 * Returns the value of the '<em><b>Poset Mask</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Poset Mask</em>' containment reference.
	 * @see #setPosetMask(Mask)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getMonotonicityInfo_PosetMask()
	 * @model containment="true"
	 * @generated
	 */
	Mask getPosetMask();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.MonotonicityInfo#getPosetMask <em>Poset Mask</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Poset Mask</em>' containment reference.
	 * @see #getPosetMask()
	 * @generated
	 */
	void setPosetMask(Mask value);

	/**
	 * Returns the value of the '<em><b>Poset Comparator</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Poset Comparator</em>' attribute.
	 * @see #setPosetComparator(Object)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getMonotonicityInfo_PosetComparator()
	 * @model
	 * @generated
	 */
	Object getPosetComparator();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.MonotonicityInfo#getPosetComparator <em>Poset Comparator</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Poset Comparator</em>' attribute.
	 * @see #getPosetComparator()
	 * @generated
	 */
	void setPosetComparator(Object value);

} // MonotonicityInfo
