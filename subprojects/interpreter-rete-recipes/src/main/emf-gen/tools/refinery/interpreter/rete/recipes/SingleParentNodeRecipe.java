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


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Single Parent Node Recipe</b></em>'.
 * <!-- end-user-doc -->
 *
 * <!-- begin-model-doc -->
 * Abstract base class for single-parent node recipes.
 * <!-- end-model-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.SingleParentNodeRecipe#getParent <em>Parent</em>}</li>
 * </ul>
 *
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getSingleParentNodeRecipe()
 * @model abstract="true"
 * @generated
 */
public interface SingleParentNodeRecipe extends ReteNodeRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * Returns the value of the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Parent</em>' reference.
	 * @see #setParent(ReteNodeRecipe)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getSingleParentNodeRecipe_Parent()
	 * @model
	 * @generated
	 */
	ReteNodeRecipe getParent();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.SingleParentNodeRecipe#getParent <em>Parent</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Parent</em>' reference.
	 * @see #getParent()
	 * @generated
	 */
	void setParent(ReteNodeRecipe value);

} // SingleParentNodeRecipe
