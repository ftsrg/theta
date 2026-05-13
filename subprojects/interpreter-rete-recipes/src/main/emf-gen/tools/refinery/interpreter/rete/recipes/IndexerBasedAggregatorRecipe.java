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
 * A representation of the model object '<em><b>Indexer Based Aggregator Recipe</b></em>'.
 * <!-- end-user-doc -->
 *
 * <!-- begin-model-doc -->
 * Represents a (compound) node that performs an aggregation operation.
 * Parent must be a ProjectionIndexer, which defines how tuples are to be aggregated.
 * Usable only through an Join with an AggregatorIndexer as the right parent
 * <!-- end-model-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.IndexerBasedAggregatorRecipe#getParent <em>Parent</em>}</li>
 * </ul>
 *
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getIndexerBasedAggregatorRecipe()
 * @model abstract="true"
 * @generated
 */
public interface IndexerBasedAggregatorRecipe extends ReteNodeRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * Returns the value of the '<em><b>Parent</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Parent</em>' containment reference.
	 * @see #setParent(ProjectionIndexerRecipe)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getIndexerBasedAggregatorRecipe_Parent()
	 * @model containment="true"
	 * @generated
	 */
	ProjectionIndexerRecipe getParent();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.IndexerBasedAggregatorRecipe#getParent <em>Parent</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Parent</em>' containment reference.
	 * @see #getParent()
	 * @generated
	 */
	void setParent(ProjectionIndexerRecipe value);

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @model kind="operation" unique="false"
	 * @generated
	 */
	int getArity();

} // IndexerBasedAggregatorRecipe
