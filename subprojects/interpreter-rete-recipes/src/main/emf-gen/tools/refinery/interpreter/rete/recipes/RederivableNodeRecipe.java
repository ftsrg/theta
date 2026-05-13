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

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Rederivable Node Recipe</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.RederivableNodeRecipe#isDeleteRederiveEvaluation <em>Delete Rederive Evaluation</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.RederivableNodeRecipe#getOptionalMonotonicityInfo <em>Optional Monotonicity Info</em>}</li>
 * </ul>
 *
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getRederivableNodeRecipe()
 * @model abstract="true"
 * @generated
 */
public interface RederivableNodeRecipe extends EObject
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * Returns the value of the '<em><b>Delete Rederive Evaluation</b></em>' attribute.
	 * The default value is <code>"false"</code>.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Delete Rederive Evaluation</em>' attribute.
	 * @see #setDeleteRederiveEvaluation(boolean)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getRederivableNodeRecipe_DeleteRederiveEvaluation()
	 * @model default="false"
	 * @generated
	 */
	boolean isDeleteRederiveEvaluation();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.RederivableNodeRecipe#isDeleteRederiveEvaluation <em>Delete Rederive Evaluation</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Delete Rederive Evaluation</em>' attribute.
	 * @see #isDeleteRederiveEvaluation()
	 * @generated
	 */
	void setDeleteRederiveEvaluation(boolean value);

	/**
	 * Returns the value of the '<em><b>Optional Monotonicity Info</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Optional Monotonicity Info</em>' containment reference.
	 * @see #setOptionalMonotonicityInfo(MonotonicityInfo)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getRederivableNodeRecipe_OptionalMonotonicityInfo()
	 * @model containment="true" resolveProxies="true"
	 * @generated
	 */
	MonotonicityInfo getOptionalMonotonicityInfo();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.RederivableNodeRecipe#getOptionalMonotonicityInfo <em>Optional Monotonicity Info</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Optional Monotonicity Info</em>' containment reference.
	 * @see #getOptionalMonotonicityInfo()
	 * @generated
	 */
	void setOptionalMonotonicityInfo(MonotonicityInfo value);

} // RederivableNodeRecipe
