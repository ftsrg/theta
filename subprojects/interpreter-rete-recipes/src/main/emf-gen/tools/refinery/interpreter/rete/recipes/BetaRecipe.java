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
 * A representation of the model object '<em><b>Beta Recipe</b></em>'.
 * <!-- end-user-doc -->
 *
 * <!-- begin-model-doc -->
 * Abstract base class for Beta node recipes.
 * <!-- end-model-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.BetaRecipe#getLeftParent <em>Left Parent</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.BetaRecipe#getRightParent <em>Right Parent</em>}</li>
 * </ul>
 *
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getBetaRecipe()
 * @model abstract="true"
 * @generated
 */
public interface BetaRecipe extends ReteNodeRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * Returns the value of the '<em><b>Left Parent</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Left Parent</em>' containment reference.
	 * @see #setLeftParent(ProjectionIndexerRecipe)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getBetaRecipe_LeftParent()
	 * @model containment="true"
	 * @generated
	 */
	ProjectionIndexerRecipe getLeftParent();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.BetaRecipe#getLeftParent <em>Left Parent</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Left Parent</em>' containment reference.
	 * @see #getLeftParent()
	 * @generated
	 */
	void setLeftParent(ProjectionIndexerRecipe value);

	/**
	 * Returns the value of the '<em><b>Right Parent</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * <!-- begin-model-doc -->
	 *  can be an AggregatorIndexer
	 * <!-- end-model-doc -->
	 * @return the value of the '<em>Right Parent</em>' containment reference.
	 * @see #setRightParent(IndexerRecipe)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getBetaRecipe_RightParent()
	 * @model containment="true"
	 * @generated
	 */
	IndexerRecipe getRightParent();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.BetaRecipe#getRightParent <em>Right Parent</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Right Parent</em>' containment reference.
	 * @see #getRightParent()
	 * @generated
	 */
	void setRightParent(IndexerRecipe value);

} // BetaRecipe
