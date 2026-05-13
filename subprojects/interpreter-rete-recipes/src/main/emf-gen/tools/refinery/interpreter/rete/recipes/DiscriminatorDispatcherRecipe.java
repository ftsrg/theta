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
 * A representation of the model object '<em><b>Discriminator Dispatcher Recipe</b></em>'.
 * <!-- end-user-doc -->
 *
 * <!-- begin-model-doc -->
 * Node that sends tuples off to different buckets (attached as children) based on the value of a given column.
 * <!-- end-model-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.DiscriminatorDispatcherRecipe#getDiscriminationColumnIndex <em>Discrimination Column Index</em>}</li>
 * </ul>
 *
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getDiscriminatorDispatcherRecipe()
 * @model
 * @generated
 */
public interface DiscriminatorDispatcherRecipe extends SingleParentNodeRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * Returns the value of the '<em><b>Discrimination Column Index</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Discrimination Column Index</em>' attribute.
	 * @see #setDiscriminationColumnIndex(int)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getDiscriminatorDispatcherRecipe_DiscriminationColumnIndex()
	 * @model
	 * @generated
	 */
	int getDiscriminationColumnIndex();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.DiscriminatorDispatcherRecipe#getDiscriminationColumnIndex <em>Discrimination Column Index</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Discrimination Column Index</em>' attribute.
	 * @see #getDiscriminationColumnIndex()
	 * @generated
	 */
	void setDiscriminationColumnIndex(int value);

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @model kind="operation" unique="false"
	 * @generated
	 */
	int getArity();

} // DiscriminatorDispatcherRecipe
