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

import tools.refinery.interpreter.matchers.psystem.aggregations.IMultisetAggregationOperator;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Single Column Aggregator Recipe</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe#getMultisetAggregationOperator <em>Multiset Aggregation Operator</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe#getAggregableIndex <em>Aggregable Index</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe#getGroupByMask <em>Group By Mask</em>}</li>
 * </ul>
 *
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getSingleColumnAggregatorRecipe()
 * @model
 * @generated
 */
public interface SingleColumnAggregatorRecipe extends AlphaRecipe, RederivableNodeRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * Returns the value of the '<em><b>Multiset Aggregation Operator</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Multiset Aggregation Operator</em>' attribute.
	 * @see #setMultisetAggregationOperator(IMultisetAggregationOperator)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getSingleColumnAggregatorRecipe_MultisetAggregationOperator()
	 * @model dataType="tools.refinery.interpreter.rete.recipes.AggregationOperator"
	 * @generated
	 */
	IMultisetAggregationOperator<?, ?, ?> getMultisetAggregationOperator();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe#getMultisetAggregationOperator <em>Multiset Aggregation Operator</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Multiset Aggregation Operator</em>' attribute.
	 * @see #getMultisetAggregationOperator()
	 * @generated
	 */
	void setMultisetAggregationOperator(IMultisetAggregationOperator<?, ?, ?> value);

	/**
	 * Returns the value of the '<em><b>Aggregable Index</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Aggregable Index</em>' attribute.
	 * @see #setAggregableIndex(int)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getSingleColumnAggregatorRecipe_AggregableIndex()
	 * @model
	 * @generated
	 */
	int getAggregableIndex();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe#getAggregableIndex <em>Aggregable Index</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Aggregable Index</em>' attribute.
	 * @see #getAggregableIndex()
	 * @generated
	 */
	void setAggregableIndex(int value);

	/**
	 * Returns the value of the '<em><b>Group By Mask</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Group By Mask</em>' containment reference.
	 * @see #setGroupByMask(Mask)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getSingleColumnAggregatorRecipe_GroupByMask()
	 * @model containment="true" resolveProxies="true" required="true"
	 * @generated
	 */
	Mask getGroupByMask();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe#getGroupByMask <em>Group By Mask</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Group By Mask</em>' containment reference.
	 * @see #getGroupByMask()
	 * @generated
	 */
	void setGroupByMask(Mask value);

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @model kind="operation" unique="false"
	 * @generated
	 */
	int getArity();

} // SingleColumnAggregatorRecipe
