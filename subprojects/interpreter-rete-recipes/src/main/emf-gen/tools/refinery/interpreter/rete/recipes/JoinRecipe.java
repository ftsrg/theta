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
 * A representation of the model object '<em><b>Join Recipe</b></em>'.
 * <!-- end-user-doc -->
 *
 * <!-- begin-model-doc -->
 * The most basic beta operation, the join node performs a join operation over two input tuple sets.
 * <!-- end-model-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.JoinRecipe#getRightParentComplementaryMask <em>Right Parent Complementary Mask</em>}</li>
 * </ul>
 *
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getJoinRecipe()
 * @model
 * @generated
 */
public interface JoinRecipe extends BetaRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * Returns the value of the '<em><b>Right Parent Complementary Mask</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Right Parent Complementary Mask</em>' containment reference.
	 * @see #setRightParentComplementaryMask(Mask)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getJoinRecipe_RightParentComplementaryMask()
	 * @model containment="true"
	 * @generated
	 */
	Mask getRightParentComplementaryMask();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.JoinRecipe#getRightParentComplementaryMask <em>Right Parent Complementary Mask</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Right Parent Complementary Mask</em>' containment reference.
	 * @see #getRightParentComplementaryMask()
	 * @generated
	 */
	void setRightParentComplementaryMask(Mask value);

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @model kind="operation" unique="false"
	 * @generated
	 */
	int getArity();

} // JoinRecipe
