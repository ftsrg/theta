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
 * A representation of the model object '<em><b>Indexer Recipe</b></em>'.
 * <!-- end-user-doc -->
 *
 * <!-- begin-model-doc -->
 * Represents a node that indexes the contents of a parent based on a projection defined by a Mask.
 * <!-- end-model-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.IndexerRecipe#getMask <em>Mask</em>}</li>
 * </ul>
 *
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getIndexerRecipe()
 * @model abstract="true"
 * @generated
 */
public interface IndexerRecipe extends SingleParentNodeRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * Returns the value of the '<em><b>Mask</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Mask</em>' containment reference.
	 * @see #setMask(Mask)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getIndexerRecipe_Mask()
	 * @model containment="true"
	 * @generated
	 */
	Mask getMask();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.IndexerRecipe#getMask <em>Mask</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Mask</em>' containment reference.
	 * @see #getMask()
	 * @generated
	 */
	void setMask(Mask value);

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @model kind="operation" unique="false"
	 * @generated
	 */
	int getArity();

} // IndexerRecipe
