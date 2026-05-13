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
 * A representation of the model object '<em><b>Production Recipe</b></em>'.
 * <!-- end-user-doc -->
 *
 * <!-- begin-model-doc -->
 * The production node represents the output of the Rete network,
 * from which the results of a query can be read.
 * <!-- end-model-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.ProductionRecipe#getMappedIndices <em>Mapped Indices</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.ProductionRecipe#getPattern <em>Pattern</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.ProductionRecipe#getPatternFQN <em>Pattern FQN</em>}</li>
 * </ul>
 *
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getProductionRecipe()
 * @model
 * @generated
 */
public interface ProductionRecipe extends MultiParentNodeRecipe, RederivableNodeRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * Returns the value of the '<em><b>Mapped Indices</b></em>' map.
	 * The key is of type {@link java.lang.String},
	 * and the value is of type {@link java.lang.Integer},
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * <!-- begin-model-doc -->
	 * String -> Index map.
	 * Indicates the positions of parameters.
	 * <!-- end-model-doc -->
	 * @return the value of the '<em>Mapped Indices</em>' map.
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getProductionRecipe_MappedIndices()
	 * @model mapType="tools.refinery.interpreter.rete.recipes.StringIndexMapEntry&lt;org.eclipse.emf.ecore.EString, tools.refinery.interpreter.rete.recipes.Index&gt;"
	 * @generated
	 */
	EMap<String, Integer> getMappedIndices();

	/**
	 * Returns the value of the '<em><b>Pattern</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * <!-- begin-model-doc -->
	 * Traceability link to defining pattern object (from EMFPatternLanguage)
	 * TODO unused?
	 * <!-- end-model-doc -->
	 * @return the value of the '<em>Pattern</em>' attribute.
	 * @see #setPattern(Object)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getProductionRecipe_Pattern()
	 * @model unique="false"
	 * @generated
	 */
	Object getPattern();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.ProductionRecipe#getPattern <em>Pattern</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Pattern</em>' attribute.
	 * @see #getPattern()
	 * @generated
	 */
	void setPattern(Object value);

	/**
	 * Returns the value of the '<em><b>Pattern FQN</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Pattern FQN</em>' attribute.
	 * @see #setPatternFQN(String)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getProductionRecipe_PatternFQN()
	 * @model
	 * @generated
	 */
	String getPatternFQN();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.ProductionRecipe#getPatternFQN <em>Pattern FQN</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Pattern FQN</em>' attribute.
	 * @see #getPatternFQN()
	 * @generated
	 */
	void setPatternFQN(String value);

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @model kind="operation" unique="false"
	 * @generated
	 */
	int getArity();

} // ProductionRecipe
