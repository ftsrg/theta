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
 * A representation of the model object '<em><b>Input Recipe</b></em>'.
 * <!-- end-user-doc -->
 *
 * <!-- begin-model-doc -->
 * Represents input nodes for the Rete network, i.e. nodes
 * that generate input tuples for processing.
 * <!-- end-model-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.InputRecipe#getInputKey <em>Input Key</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.InputRecipe#getKeyID <em>Key ID</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.InputRecipe#getKeyArity <em>Key Arity</em>}</li>
 * </ul>
 *
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getInputRecipe()
 * @model
 * @generated
 */
public interface InputRecipe extends ReteNodeRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * Returns the value of the '<em><b>Input Key</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Input Key</em>' attribute.
	 * @see #setInputKey(Object)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getInputRecipe_InputKey()
	 * @model transient="true"
	 * @generated
	 */
	Object getInputKey();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.InputRecipe#getInputKey <em>Input Key</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Input Key</em>' attribute.
	 * @see #getInputKey()
	 * @generated
	 */
	void setInputKey(Object value);

	/**
	 * Returns the value of the '<em><b>Key ID</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * <!-- begin-model-doc -->
	 * Temporary construct for identifying types over the wire.
	 * TODO improve type references
	 * <!-- end-model-doc -->
	 * @return the value of the '<em>Key ID</em>' attribute.
	 * @see #setKeyID(String)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getInputRecipe_KeyID()
	 * @model unique="false"
	 * @generated
	 */
	String getKeyID();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.InputRecipe#getKeyID <em>Key ID</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Key ID</em>' attribute.
	 * @see #getKeyID()
	 * @generated
	 */
	void setKeyID(String value);

	/**
	 * Returns the value of the '<em><b>Key Arity</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Key Arity</em>' attribute.
	 * @see #setKeyArity(int)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getInputRecipe_KeyArity()
	 * @model
	 * @generated
	 */
	int getKeyArity();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.InputRecipe#getKeyArity <em>Key Arity</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Key Arity</em>' attribute.
	 * @see #getKeyArity()
	 * @generated
	 */
	void setKeyArity(int value);

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @model kind="operation" unique="false"
	 * @generated
	 */
	int getArity();

} // InputRecipe
