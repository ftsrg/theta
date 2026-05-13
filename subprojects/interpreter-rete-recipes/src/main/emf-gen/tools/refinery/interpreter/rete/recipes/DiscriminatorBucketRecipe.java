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
 * A representation of the model object '<em><b>Discriminator Bucket Recipe</b></em>'.
 * <!-- end-user-doc -->
 *
 * <!-- begin-model-doc -->
 * A bucket holds a filtered set of tuples of its parent DiscriminatorDispatcher; exactly those that have the given bucket key at their discrimination column.
 * <!-- end-model-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.DiscriminatorBucketRecipe#getBucketKey <em>Bucket Key</em>}</li>
 * </ul>
 *
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getDiscriminatorBucketRecipe()
 * @model
 * @generated
 */
public interface DiscriminatorBucketRecipe extends SingleParentNodeRecipe
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * Returns the value of the '<em><b>Bucket Key</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Bucket Key</em>' attribute.
	 * @see #setBucketKey(Object)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getDiscriminatorBucketRecipe_BucketKey()
	 * @model
	 * @generated
	 */
	Object getBucketKey();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.DiscriminatorBucketRecipe#getBucketKey <em>Bucket Key</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Bucket Key</em>' attribute.
	 * @see #getBucketKey()
	 * @generated
	 */
	void setBucketKey(Object value);

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @model kind="operation" unique="false"
	 * @generated
	 */
	int getArity();

} // DiscriminatorBucketRecipe
