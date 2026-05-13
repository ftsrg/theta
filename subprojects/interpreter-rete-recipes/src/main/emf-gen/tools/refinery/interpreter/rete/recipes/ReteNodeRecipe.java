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
 * A representation of the model object '<em><b>Rete Node Recipe</b></em>'.
 * <!-- end-user-doc -->
 *
 * <!-- begin-model-doc -->
 * Abstract base class for model elements that represent "Rete node recipes",
 * that is DTOs that carry information for Rete network construction.
 * 
 * @noimplement
 * <!-- end-model-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.ReteNodeRecipe#getTraceInfo <em>Trace Info</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.ReteNodeRecipe#getEquivalenceClassIDs <em>Equivalence Class IDs</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.ReteNodeRecipe#getCachedHashCode <em>Cached Hash Code</em>}</li>
 *   <li>{@link tools.refinery.interpreter.rete.recipes.ReteNodeRecipe#isConstructed <em>Constructed</em>}</li>
 * </ul>
 *
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getReteNodeRecipe()
 * @model abstract="true"
 * @generated
 */
public interface ReteNodeRecipe extends EObject
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * Returns the value of the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * <!-- begin-model-doc -->
	 * Temporary construct for storing traceability information.
	 * <!-- end-model-doc -->
	 * @return the value of the '<em>Trace Info</em>' attribute.
	 * @see #setTraceInfo(String)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getReteNodeRecipe_TraceInfo()
	 * @model unique="false"
	 * @generated
	 */
	String getTraceInfo();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.ReteNodeRecipe#getTraceInfo <em>Trace Info</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Trace Info</em>' attribute.
	 * @see #getTraceInfo()
	 * @generated
	 */
	void setTraceInfo(String value);

	/**
	 * Returns the value of the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * The list contents are of type {@link java.lang.Long}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * <!-- begin-model-doc -->
	 * If two recipes were found equivalent, a matching equivalence ID can be assigned to them by {@link RecipeRecognizer}. 
	 * If two recipes share (at least one) equivalence ID, they are known to be equivalent.
	 * 
	 * <p>
	 * A difference in this attribute only does not preclude two recipe elements to be considered equal. 
	 * If they are shown to be equivalent using deeper analysis, equivalence ids can be set so that the equivalence is recognized more easily the next time.
	 * 
	 * @since 1.3
	 * <!-- end-model-doc -->
	 * @return the value of the '<em>Equivalence Class IDs</em>' attribute list.
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getReteNodeRecipe_EquivalenceClassIDs()
	 * @model transient="true"
	 * @generated
	 */
	EList<Long> getEquivalenceClassIDs();

	/**
	 * Returns the value of the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Cached Hash Code</em>' attribute.
	 * @see #setCachedHashCode(Long)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getReteNodeRecipe_CachedHashCode()
	 * @model
	 * @generated
	 */
	Long getCachedHashCode();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.ReteNodeRecipe#getCachedHashCode <em>Cached Hash Code</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Cached Hash Code</em>' attribute.
	 * @see #getCachedHashCode()
	 * @generated
	 */
	void setCachedHashCode(Long value);

	/**
	 * Returns the value of the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Constructed</em>' attribute.
	 * @see #setConstructed(boolean)
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#getReteNodeRecipe_Constructed()
	 * @model
	 * @generated
	 */
	boolean isConstructed();

	/**
	 * Sets the value of the '{@link tools.refinery.interpreter.rete.recipes.ReteNodeRecipe#isConstructed <em>Constructed</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Constructed</em>' attribute.
	 * @see #isConstructed()
	 * @generated
	 */
	void setConstructed(boolean value);

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * <!-- begin-model-doc -->
	 *  The width of tuples contained by this node.
	 * <!-- end-model-doc -->
	 * @model kind="operation" unique="false"
	 * @generated
	 */
	int getArity();

} // ReteNodeRecipe
