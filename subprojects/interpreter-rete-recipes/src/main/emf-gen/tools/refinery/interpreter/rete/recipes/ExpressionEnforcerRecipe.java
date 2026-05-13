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

import org.eclipse.emf.common.util.EMap;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Expression Enforcer Recipe</b></em>'.
 * <!-- end-user-doc -->
 *
 * <!-- begin-model-doc -->
 * type RuntimeExpressionEvaluator wraps psystem.matchers.tools.refinery.interpreter.IExpressionEvaluator
 * class RuntimeExpressionDefinition extends ExpressionDefinition {
 * 	RuntimeExpressionEvaluator evaluator
 * }
 * <!-- end-model-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.ExpressionEnforcerRecipe#getExpression <em>Expression</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.ExpressionEnforcerRecipe#getMappedIndices <em>Mapped Indices</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.ExpressionEnforcerRecipe#isCacheOutput <em>Cache Output</em>}</li>
 * </ul>
 *
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getExpressionEnforcerRecipe()
 * @model abstract="true"
 * @generated
 */
public interface ExpressionEnforcerRecipe extends AlphaRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * Returns the value of the '<em><b>Expression</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * <!-- begin-model-doc -->
	 * Provides traceability to expression representation.
	 * <!-- end-model-doc -->
	 * @return the value of the '<em>Expression</em>' containment reference.
	 * @see #setExpression(ExpressionDefinition)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getExpressionEnforcerRecipe_Expression()
	 * @model containment="true"
	 * @generated
	 */
	ExpressionDefinition getExpression();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.ExpressionEnforcerRecipe#getExpression <em>Expression</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Expression</em>' containment reference.
	 * @see #getExpression()
	 * @generated
	 */
	void setExpression(ExpressionDefinition value);

	/**
	 * Returns the value of the '<em><b>Mapped Indices</b></em>' map.
	 * The key is of type {@link java.lang.String},
	 * and the value is of type {@link java.lang.Integer},
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * <!-- begin-model-doc -->
	 * String -> Index map.
	 * Maps variable names in the expression to tuple indices.
	 * <!-- end-model-doc -->
	 * @return the value of the '<em>Mapped Indices</em>' map.
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getExpressionEnforcerRecipe_MappedIndices()
	 * @model mapType="tools.refinery.interpreter.rete.recipes.StringIndexMapEntry&lt;org.eclipse.emf.ecore.EString, tools.refinery.interpreter.rete.recipes.Index&gt;"
	 * @generated
	 */
	EMap<String, Integer> getMappedIndices();

	/**
	 * Returns the value of the '<em><b>Cache Output</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Cache Output</em>' attribute.
	 * @see #setCacheOutput(boolean)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getExpressionEnforcerRecipe_CacheOutput()
	 * @model
	 * @generated
	 */
	boolean isCacheOutput();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.ExpressionEnforcerRecipe#isCacheOutput <em>Cache Output</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Cache Output</em>' attribute.
	 * @see #isCacheOutput()
	 * @generated
	 */
	void setCacheOutput(boolean value);

} // ExpressionEnforcerRecipe
