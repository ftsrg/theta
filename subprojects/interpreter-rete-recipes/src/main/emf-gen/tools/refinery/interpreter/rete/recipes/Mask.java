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

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Mask</b></em>'.
 * <!-- end-user-doc -->
 *
 * <!-- begin-model-doc -->
 * A mask defines the set of tuple variables that need to be taken into consideration for operations.
 * <!-- end-model-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.Mask#getSourceIndices <em>Source Indices</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.Mask#getSourceArity <em>Source Arity</em>}</li>
 * </ul>
 *
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getMask()
 * @model
 * @generated
 */
public interface Mask extends EObject
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * Returns the value of the '<em><b>Source Indices</b></em>' attribute list.
	 * The list contents are of type {@link java.lang.Integer}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * <!-- begin-model-doc -->
	 * The indices that are relevant for tuple operations.
	 * <!-- end-model-doc -->
	 * @return the value of the '<em>Source Indices</em>' attribute list.
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getMask_SourceIndices()
	 * @model unique="false" dataType="tools.refinery.interpreter.rete.recipes.Index"
	 * @generated
	 */
	EList<Integer> getSourceIndices();

	/**
	 * Returns the value of the '<em><b>Source Arity</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * <!-- begin-model-doc -->
	 * The arity of tuples.
	 * <!-- end-model-doc -->
	 * @return the value of the '<em>Source Arity</em>' attribute.
	 * @see #setSourceArity(int)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getMask_SourceArity()
	 * @model unique="false"
	 * @generated
	 */
	int getSourceArity();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.Mask#getSourceArity <em>Source Arity</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Source Arity</em>' attribute.
	 * @see #getSourceArity()
	 * @generated
	 */
	void setSourceArity(int value);

} // Mask
