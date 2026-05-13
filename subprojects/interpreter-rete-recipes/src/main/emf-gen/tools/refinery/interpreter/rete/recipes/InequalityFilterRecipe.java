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

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Inequality Filter Recipe</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.InequalityFilterRecipe#getSubject <em>Subject</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.InequalityFilterRecipe#getInequals <em>Inequals</em>}</li>
 * </ul>
 *
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getInequalityFilterRecipe()
 * @model
 * @generated
 */
public interface InequalityFilterRecipe extends FilterRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * Returns the value of the '<em><b>Subject</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Subject</em>' attribute.
	 * @see #setSubject(Integer)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getInequalityFilterRecipe_Subject()
	 * @model unique="false" dataType="tools.refinery.interpreter.rete.recipes.Index"
	 * @generated
	 */
	Integer getSubject();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.InequalityFilterRecipe#getSubject <em>Subject</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Subject</em>' attribute.
	 * @see #getSubject()
	 * @generated
	 */
	void setSubject(Integer value);

	/**
	 * Returns the value of the '<em><b>Inequals</b></em>' attribute list.
	 * The list contents are of type {@link java.lang.Integer}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Inequals</em>' attribute list.
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getInequalityFilterRecipe_Inequals()
	 * @model unique="false" dataType="tools.refinery.interpreter.rete.recipes.Index"
	 * @generated
	 */
	EList<Integer> getInequals();

} // InequalityFilterRecipe
