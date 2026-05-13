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

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EDataType;
import org.eclipse.emf.ecore.EOperation;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EReference;

/**
 * <!-- begin-user-doc -->
 * The <b>Package</b> for the model.
 * It contains accessors for the meta objects to represent
 * <ul>
 *   <li>each class,</li>
 *   <li>each feature of each class,</li>
 *   <li>each operation of each class,</li>
 *   <li>each enum,</li>
 *   <li>and each data type</li>
 * </ul>
 * <!-- end-user-doc -->
 * @see tools.refinery.interpreter.rete.recipes.RecipesFactory
 * @model kind="package"
 * @generated
 */
public interface RecipesPackage extends EPackage
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * The package name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNAME = "recipes"; //$NON-NLS-1$

	/**
	 * The package namespace URI.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_URI = "https://refinery.tools/emf/2023/InterpreterReteRecipes"; //$NON-NLS-1$

	/**
	 * The package namespace name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_PREFIX = "recipes"; //$NON-NLS-1$

	/**
	 * The singleton instance of the package.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	RecipesPackage eINSTANCE = tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl.init();

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.ReteRecipeImpl <em>Rete Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.ReteRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getReteRecipe()
	 * @generated
	 */
	int RETE_RECIPE = 0;

	/**
	 * The feature id for the '<em><b>Recipe Nodes</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RETE_RECIPE__RECIPE_NODES = 0;

	/**
	 * The number of structural features of the '<em>Rete Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RETE_RECIPE_FEATURE_COUNT = 1;

	/**
	 * The number of operations of the '<em>Rete Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RETE_RECIPE_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.ReteNodeRecipeImpl <em>Rete Node Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.ReteNodeRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getReteNodeRecipe()
	 * @generated
	 */
	int RETE_NODE_RECIPE = 1;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RETE_NODE_RECIPE__TRACE_INFO = 0;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int RETE_NODE_RECIPE__EQUIVALENCE_CLASS_IDS = 1;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RETE_NODE_RECIPE__CACHED_HASH_CODE = 2;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RETE_NODE_RECIPE__CONSTRUCTED = 3;

	/**
	 * The number of structural features of the '<em>Rete Node Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RETE_NODE_RECIPE_FEATURE_COUNT = 4;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RETE_NODE_RECIPE___GET_ARITY = 0;

	/**
	 * The number of operations of the '<em>Rete Node Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RETE_NODE_RECIPE_OPERATION_COUNT = 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.SingleParentNodeRecipeImpl <em>Single Parent Node Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.SingleParentNodeRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getSingleParentNodeRecipe()
	 * @generated
	 */
	int SINGLE_PARENT_NODE_RECIPE = 2;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_PARENT_NODE_RECIPE__TRACE_INFO = RETE_NODE_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int SINGLE_PARENT_NODE_RECIPE__EQUIVALENCE_CLASS_IDS = RETE_NODE_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_PARENT_NODE_RECIPE__CACHED_HASH_CODE = RETE_NODE_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_PARENT_NODE_RECIPE__CONSTRUCTED = RETE_NODE_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_PARENT_NODE_RECIPE__PARENT = RETE_NODE_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Single Parent Node Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_PARENT_NODE_RECIPE_FEATURE_COUNT = RETE_NODE_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_PARENT_NODE_RECIPE___GET_ARITY = RETE_NODE_RECIPE___GET_ARITY;

	/**
	 * The number of operations of the '<em>Single Parent Node Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_PARENT_NODE_RECIPE_OPERATION_COUNT = RETE_NODE_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.AlphaRecipeImpl <em>Alpha Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.AlphaRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getAlphaRecipe()
	 * @generated
	 */
	int ALPHA_RECIPE = 3;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ALPHA_RECIPE__TRACE_INFO = SINGLE_PARENT_NODE_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int ALPHA_RECIPE__EQUIVALENCE_CLASS_IDS = SINGLE_PARENT_NODE_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ALPHA_RECIPE__CACHED_HASH_CODE = SINGLE_PARENT_NODE_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ALPHA_RECIPE__CONSTRUCTED = SINGLE_PARENT_NODE_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ALPHA_RECIPE__PARENT = SINGLE_PARENT_NODE_RECIPE__PARENT;

	/**
	 * The number of structural features of the '<em>Alpha Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ALPHA_RECIPE_FEATURE_COUNT = SINGLE_PARENT_NODE_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ALPHA_RECIPE___GET_ARITY = SINGLE_PARENT_NODE_RECIPE___GET_ARITY;

	/**
	 * The number of operations of the '<em>Alpha Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ALPHA_RECIPE_OPERATION_COUNT = SINGLE_PARENT_NODE_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.MultiParentNodeRecipeImpl <em>Multi Parent Node Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.MultiParentNodeRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getMultiParentNodeRecipe()
	 * @generated
	 */
	int MULTI_PARENT_NODE_RECIPE = 4;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTI_PARENT_NODE_RECIPE__TRACE_INFO = RETE_NODE_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int MULTI_PARENT_NODE_RECIPE__EQUIVALENCE_CLASS_IDS = RETE_NODE_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTI_PARENT_NODE_RECIPE__CACHED_HASH_CODE = RETE_NODE_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTI_PARENT_NODE_RECIPE__CONSTRUCTED = RETE_NODE_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parents</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTI_PARENT_NODE_RECIPE__PARENTS = RETE_NODE_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Multi Parent Node Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTI_PARENT_NODE_RECIPE_FEATURE_COUNT = RETE_NODE_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTI_PARENT_NODE_RECIPE___GET_ARITY = RETE_NODE_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Multi Parent Node Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTI_PARENT_NODE_RECIPE_OPERATION_COUNT = RETE_NODE_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.MonotonicityInfoImpl <em>Monotonicity Info</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.MonotonicityInfoImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getMonotonicityInfo()
	 * @generated
	 */
	int MONOTONICITY_INFO = 5;

	/**
	 * The feature id for the '<em><b>Core Mask</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MONOTONICITY_INFO__CORE_MASK = 0;

	/**
	 * The feature id for the '<em><b>Poset Mask</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MONOTONICITY_INFO__POSET_MASK = 1;

	/**
	 * The feature id for the '<em><b>Poset Comparator</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MONOTONICITY_INFO__POSET_COMPARATOR = 2;

	/**
	 * The number of structural features of the '<em>Monotonicity Info</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MONOTONICITY_INFO_FEATURE_COUNT = 3;

	/**
	 * The number of operations of the '<em>Monotonicity Info</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MONOTONICITY_INFO_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.UniquenessEnforcerRecipeImpl <em>Uniqueness Enforcer Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.UniquenessEnforcerRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getUniquenessEnforcerRecipe()
	 * @generated
	 */
	int UNIQUENESS_ENFORCER_RECIPE = 6;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int UNIQUENESS_ENFORCER_RECIPE__TRACE_INFO = MULTI_PARENT_NODE_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int UNIQUENESS_ENFORCER_RECIPE__EQUIVALENCE_CLASS_IDS = MULTI_PARENT_NODE_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int UNIQUENESS_ENFORCER_RECIPE__CACHED_HASH_CODE = MULTI_PARENT_NODE_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int UNIQUENESS_ENFORCER_RECIPE__CONSTRUCTED = MULTI_PARENT_NODE_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parents</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int UNIQUENESS_ENFORCER_RECIPE__PARENTS = MULTI_PARENT_NODE_RECIPE__PARENTS;

	/**
	 * The feature id for the '<em><b>Delete Rederive Evaluation</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int UNIQUENESS_ENFORCER_RECIPE__DELETE_REDERIVE_EVALUATION = MULTI_PARENT_NODE_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Optional Monotonicity Info</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int UNIQUENESS_ENFORCER_RECIPE__OPTIONAL_MONOTONICITY_INFO = MULTI_PARENT_NODE_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Uniqueness Enforcer Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int UNIQUENESS_ENFORCER_RECIPE_FEATURE_COUNT = MULTI_PARENT_NODE_RECIPE_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int UNIQUENESS_ENFORCER_RECIPE___GET_ARITY = MULTI_PARENT_NODE_RECIPE___GET_ARITY;

	/**
	 * The number of operations of the '<em>Uniqueness Enforcer Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int UNIQUENESS_ENFORCER_RECIPE_OPERATION_COUNT = MULTI_PARENT_NODE_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.ProductionRecipeImpl <em>Production Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.ProductionRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getProductionRecipe()
	 * @generated
	 */
	int PRODUCTION_RECIPE = 7;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRODUCTION_RECIPE__TRACE_INFO = MULTI_PARENT_NODE_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int PRODUCTION_RECIPE__EQUIVALENCE_CLASS_IDS = MULTI_PARENT_NODE_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRODUCTION_RECIPE__CACHED_HASH_CODE = MULTI_PARENT_NODE_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRODUCTION_RECIPE__CONSTRUCTED = MULTI_PARENT_NODE_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parents</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRODUCTION_RECIPE__PARENTS = MULTI_PARENT_NODE_RECIPE__PARENTS;

	/**
	 * The feature id for the '<em><b>Delete Rederive Evaluation</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRODUCTION_RECIPE__DELETE_REDERIVE_EVALUATION = MULTI_PARENT_NODE_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Optional Monotonicity Info</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRODUCTION_RECIPE__OPTIONAL_MONOTONICITY_INFO = MULTI_PARENT_NODE_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Mapped Indices</b></em>' map.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRODUCTION_RECIPE__MAPPED_INDICES = MULTI_PARENT_NODE_RECIPE_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Pattern</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRODUCTION_RECIPE__PATTERN = MULTI_PARENT_NODE_RECIPE_FEATURE_COUNT + 3;

	/**
	 * The feature id for the '<em><b>Pattern FQN</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRODUCTION_RECIPE__PATTERN_FQN = MULTI_PARENT_NODE_RECIPE_FEATURE_COUNT + 4;

	/**
	 * The number of structural features of the '<em>Production Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRODUCTION_RECIPE_FEATURE_COUNT = MULTI_PARENT_NODE_RECIPE_FEATURE_COUNT + 5;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRODUCTION_RECIPE___GET_ARITY = MULTI_PARENT_NODE_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Production Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRODUCTION_RECIPE_OPERATION_COUNT = MULTI_PARENT_NODE_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.IndexerRecipeImpl <em>Indexer Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.IndexerRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getIndexerRecipe()
	 * @generated
	 */
	int INDEXER_RECIPE = 8;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEXER_RECIPE__TRACE_INFO = SINGLE_PARENT_NODE_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int INDEXER_RECIPE__EQUIVALENCE_CLASS_IDS = SINGLE_PARENT_NODE_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEXER_RECIPE__CACHED_HASH_CODE = SINGLE_PARENT_NODE_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEXER_RECIPE__CONSTRUCTED = SINGLE_PARENT_NODE_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEXER_RECIPE__PARENT = SINGLE_PARENT_NODE_RECIPE__PARENT;

	/**
	 * The feature id for the '<em><b>Mask</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEXER_RECIPE__MASK = SINGLE_PARENT_NODE_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Indexer Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEXER_RECIPE_FEATURE_COUNT = SINGLE_PARENT_NODE_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEXER_RECIPE___GET_ARITY = SINGLE_PARENT_NODE_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Indexer Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEXER_RECIPE_OPERATION_COUNT = SINGLE_PARENT_NODE_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.ProjectionIndexerRecipeImpl <em>Projection Indexer Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.ProjectionIndexerRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getProjectionIndexerRecipe()
	 * @generated
	 */
	int PROJECTION_INDEXER_RECIPE = 9;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROJECTION_INDEXER_RECIPE__TRACE_INFO = INDEXER_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int PROJECTION_INDEXER_RECIPE__EQUIVALENCE_CLASS_IDS = INDEXER_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROJECTION_INDEXER_RECIPE__CACHED_HASH_CODE = INDEXER_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROJECTION_INDEXER_RECIPE__CONSTRUCTED = INDEXER_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROJECTION_INDEXER_RECIPE__PARENT = INDEXER_RECIPE__PARENT;

	/**
	 * The feature id for the '<em><b>Mask</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROJECTION_INDEXER_RECIPE__MASK = INDEXER_RECIPE__MASK;

	/**
	 * The number of structural features of the '<em>Projection Indexer Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROJECTION_INDEXER_RECIPE_FEATURE_COUNT = INDEXER_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROJECTION_INDEXER_RECIPE___GET_ARITY = INDEXER_RECIPE___GET_ARITY;

	/**
	 * The number of operations of the '<em>Projection Indexer Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROJECTION_INDEXER_RECIPE_OPERATION_COUNT = INDEXER_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.AggregatorIndexerRecipeImpl <em>Aggregator Indexer Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.AggregatorIndexerRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getAggregatorIndexerRecipe()
	 * @generated
	 */
	int AGGREGATOR_INDEXER_RECIPE = 10;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATOR_INDEXER_RECIPE__TRACE_INFO = INDEXER_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int AGGREGATOR_INDEXER_RECIPE__EQUIVALENCE_CLASS_IDS = INDEXER_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATOR_INDEXER_RECIPE__CACHED_HASH_CODE = INDEXER_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATOR_INDEXER_RECIPE__CONSTRUCTED = INDEXER_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATOR_INDEXER_RECIPE__PARENT = INDEXER_RECIPE__PARENT;

	/**
	 * The feature id for the '<em><b>Mask</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATOR_INDEXER_RECIPE__MASK = INDEXER_RECIPE__MASK;

	/**
	 * The number of structural features of the '<em>Aggregator Indexer Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATOR_INDEXER_RECIPE_FEATURE_COUNT = INDEXER_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATOR_INDEXER_RECIPE___GET_ARITY = INDEXER_RECIPE___GET_ARITY;

	/**
	 * The number of operations of the '<em>Aggregator Indexer Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATOR_INDEXER_RECIPE_OPERATION_COUNT = INDEXER_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.BetaRecipeImpl <em>Beta Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.BetaRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getBetaRecipe()
	 * @generated
	 */
	int BETA_RECIPE = 11;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BETA_RECIPE__TRACE_INFO = RETE_NODE_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int BETA_RECIPE__EQUIVALENCE_CLASS_IDS = RETE_NODE_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BETA_RECIPE__CACHED_HASH_CODE = RETE_NODE_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BETA_RECIPE__CONSTRUCTED = RETE_NODE_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Left Parent</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BETA_RECIPE__LEFT_PARENT = RETE_NODE_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right Parent</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BETA_RECIPE__RIGHT_PARENT = RETE_NODE_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Beta Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BETA_RECIPE_FEATURE_COUNT = RETE_NODE_RECIPE_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BETA_RECIPE___GET_ARITY = RETE_NODE_RECIPE___GET_ARITY;

	/**
	 * The number of operations of the '<em>Beta Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BETA_RECIPE_OPERATION_COUNT = RETE_NODE_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.MaskImpl <em>Mask</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.MaskImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getMask()
	 * @generated
	 */
	int MASK = 12;

	/**
	 * The feature id for the '<em><b>Source Indices</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MASK__SOURCE_INDICES = 0;

	/**
	 * The feature id for the '<em><b>Source Arity</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MASK__SOURCE_ARITY = 1;

	/**
	 * The number of structural features of the '<em>Mask</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MASK_FEATURE_COUNT = 2;

	/**
	 * The number of operations of the '<em>Mask</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MASK_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.StringIndexMapEntryImpl <em>String Index Map Entry</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.StringIndexMapEntryImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getStringIndexMapEntry()
	 * @generated
	 */
	int STRING_INDEX_MAP_ENTRY = 13;

	/**
	 * The feature id for the '<em><b>Key</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_INDEX_MAP_ENTRY__KEY = 0;

	/**
	 * The feature id for the '<em><b>Value</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_INDEX_MAP_ENTRY__VALUE = 1;

	/**
	 * The number of structural features of the '<em>String Index Map Entry</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_INDEX_MAP_ENTRY_FEATURE_COUNT = 2;

	/**
	 * The number of operations of the '<em>String Index Map Entry</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_INDEX_MAP_ENTRY_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.InputRecipeImpl <em>Input Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.InputRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getInputRecipe()
	 * @generated
	 */
	int INPUT_RECIPE = 14;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_RECIPE__TRACE_INFO = RETE_NODE_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int INPUT_RECIPE__EQUIVALENCE_CLASS_IDS = RETE_NODE_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_RECIPE__CACHED_HASH_CODE = RETE_NODE_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_RECIPE__CONSTRUCTED = RETE_NODE_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Input Key</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_RECIPE__INPUT_KEY = RETE_NODE_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Key ID</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_RECIPE__KEY_ID = RETE_NODE_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Key Arity</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_RECIPE__KEY_ARITY = RETE_NODE_RECIPE_FEATURE_COUNT + 2;

	/**
	 * The number of structural features of the '<em>Input Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_RECIPE_FEATURE_COUNT = RETE_NODE_RECIPE_FEATURE_COUNT + 3;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_RECIPE___GET_ARITY = RETE_NODE_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Input Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_RECIPE_OPERATION_COUNT = RETE_NODE_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.ConstantRecipeImpl <em>Constant Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.ConstantRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getConstantRecipe()
	 * @generated
	 */
	int CONSTANT_RECIPE = 15;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONSTANT_RECIPE__TRACE_INFO = RETE_NODE_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int CONSTANT_RECIPE__EQUIVALENCE_CLASS_IDS = RETE_NODE_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONSTANT_RECIPE__CACHED_HASH_CODE = RETE_NODE_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONSTANT_RECIPE__CONSTRUCTED = RETE_NODE_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Constant Values</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONSTANT_RECIPE__CONSTANT_VALUES = RETE_NODE_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Constant Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONSTANT_RECIPE_FEATURE_COUNT = RETE_NODE_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONSTANT_RECIPE___GET_ARITY = RETE_NODE_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Constant Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONSTANT_RECIPE_OPERATION_COUNT = RETE_NODE_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.TransitiveClosureRecipeImpl <em>Transitive Closure Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.TransitiveClosureRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getTransitiveClosureRecipe()
	 * @generated
	 */
	int TRANSITIVE_CLOSURE_RECIPE = 16;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRANSITIVE_CLOSURE_RECIPE__TRACE_INFO = ALPHA_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int TRANSITIVE_CLOSURE_RECIPE__EQUIVALENCE_CLASS_IDS = ALPHA_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRANSITIVE_CLOSURE_RECIPE__CACHED_HASH_CODE = ALPHA_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRANSITIVE_CLOSURE_RECIPE__CONSTRUCTED = ALPHA_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRANSITIVE_CLOSURE_RECIPE__PARENT = ALPHA_RECIPE__PARENT;

	/**
	 * The number of structural features of the '<em>Transitive Closure Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRANSITIVE_CLOSURE_RECIPE_FEATURE_COUNT = ALPHA_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRANSITIVE_CLOSURE_RECIPE___GET_ARITY = ALPHA_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Transitive Closure Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRANSITIVE_CLOSURE_RECIPE_OPERATION_COUNT = ALPHA_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.FilterRecipeImpl <em>Filter Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.FilterRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getFilterRecipe()
	 * @generated
	 */
	int FILTER_RECIPE = 17;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FILTER_RECIPE__TRACE_INFO = ALPHA_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int FILTER_RECIPE__EQUIVALENCE_CLASS_IDS = ALPHA_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FILTER_RECIPE__CACHED_HASH_CODE = ALPHA_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FILTER_RECIPE__CONSTRUCTED = ALPHA_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FILTER_RECIPE__PARENT = ALPHA_RECIPE__PARENT;

	/**
	 * The number of structural features of the '<em>Filter Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FILTER_RECIPE_FEATURE_COUNT = ALPHA_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FILTER_RECIPE___GET_ARITY = ALPHA_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Filter Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FILTER_RECIPE_OPERATION_COUNT = ALPHA_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.InequalityFilterRecipeImpl <em>Inequality Filter Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.InequalityFilterRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getInequalityFilterRecipe()
	 * @generated
	 */
	int INEQUALITY_FILTER_RECIPE = 18;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY_FILTER_RECIPE__TRACE_INFO = FILTER_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int INEQUALITY_FILTER_RECIPE__EQUIVALENCE_CLASS_IDS = FILTER_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY_FILTER_RECIPE__CACHED_HASH_CODE = FILTER_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY_FILTER_RECIPE__CONSTRUCTED = FILTER_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY_FILTER_RECIPE__PARENT = FILTER_RECIPE__PARENT;

	/**
	 * The feature id for the '<em><b>Subject</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY_FILTER_RECIPE__SUBJECT = FILTER_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Inequals</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY_FILTER_RECIPE__INEQUALS = FILTER_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Inequality Filter Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY_FILTER_RECIPE_FEATURE_COUNT = FILTER_RECIPE_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY_FILTER_RECIPE___GET_ARITY = FILTER_RECIPE___GET_ARITY;

	/**
	 * The number of operations of the '<em>Inequality Filter Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY_FILTER_RECIPE_OPERATION_COUNT = FILTER_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.EqualityFilterRecipeImpl <em>Equality Filter Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.EqualityFilterRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getEqualityFilterRecipe()
	 * @generated
	 */
	int EQUALITY_FILTER_RECIPE = 19;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY_FILTER_RECIPE__TRACE_INFO = FILTER_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int EQUALITY_FILTER_RECIPE__EQUIVALENCE_CLASS_IDS = FILTER_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY_FILTER_RECIPE__CACHED_HASH_CODE = FILTER_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY_FILTER_RECIPE__CONSTRUCTED = FILTER_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY_FILTER_RECIPE__PARENT = FILTER_RECIPE__PARENT;

	/**
	 * The feature id for the '<em><b>Indices</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY_FILTER_RECIPE__INDICES = FILTER_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Equality Filter Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY_FILTER_RECIPE_FEATURE_COUNT = FILTER_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY_FILTER_RECIPE___GET_ARITY = FILTER_RECIPE___GET_ARITY;

	/**
	 * The number of operations of the '<em>Equality Filter Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY_FILTER_RECIPE_OPERATION_COUNT = FILTER_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.TransparentRecipeImpl <em>Transparent Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.TransparentRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getTransparentRecipe()
	 * @generated
	 */
	int TRANSPARENT_RECIPE = 20;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRANSPARENT_RECIPE__TRACE_INFO = FILTER_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int TRANSPARENT_RECIPE__EQUIVALENCE_CLASS_IDS = FILTER_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRANSPARENT_RECIPE__CACHED_HASH_CODE = FILTER_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRANSPARENT_RECIPE__CONSTRUCTED = FILTER_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRANSPARENT_RECIPE__PARENT = FILTER_RECIPE__PARENT;

	/**
	 * The number of structural features of the '<em>Transparent Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRANSPARENT_RECIPE_FEATURE_COUNT = FILTER_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRANSPARENT_RECIPE___GET_ARITY = FILTER_RECIPE___GET_ARITY;

	/**
	 * The number of operations of the '<em>Transparent Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRANSPARENT_RECIPE_OPERATION_COUNT = FILTER_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.TrimmerRecipeImpl <em>Trimmer Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.TrimmerRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getTrimmerRecipe()
	 * @generated
	 */
	int TRIMMER_RECIPE = 21;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRIMMER_RECIPE__TRACE_INFO = ALPHA_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int TRIMMER_RECIPE__EQUIVALENCE_CLASS_IDS = ALPHA_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRIMMER_RECIPE__CACHED_HASH_CODE = ALPHA_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRIMMER_RECIPE__CONSTRUCTED = ALPHA_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRIMMER_RECIPE__PARENT = ALPHA_RECIPE__PARENT;

	/**
	 * The feature id for the '<em><b>Mask</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRIMMER_RECIPE__MASK = ALPHA_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Trimmer Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRIMMER_RECIPE_FEATURE_COUNT = ALPHA_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRIMMER_RECIPE___GET_ARITY = ALPHA_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Trimmer Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TRIMMER_RECIPE_OPERATION_COUNT = ALPHA_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.ExpressionDefinitionImpl <em>Expression Definition</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.ExpressionDefinitionImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getExpressionDefinition()
	 * @generated
	 */
	int EXPRESSION_DEFINITION = 22;

	/**
	 * The feature id for the '<em><b>Evaluator</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_DEFINITION__EVALUATOR = 0;

	/**
	 * The number of structural features of the '<em>Expression Definition</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_DEFINITION_FEATURE_COUNT = 1;

	/**
	 * The number of operations of the '<em>Expression Definition</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_DEFINITION_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.ExpressionEnforcerRecipeImpl <em>Expression Enforcer Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.ExpressionEnforcerRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getExpressionEnforcerRecipe()
	 * @generated
	 */
	int EXPRESSION_ENFORCER_RECIPE = 23;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_ENFORCER_RECIPE__TRACE_INFO = ALPHA_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_ENFORCER_RECIPE__EQUIVALENCE_CLASS_IDS = ALPHA_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_ENFORCER_RECIPE__CACHED_HASH_CODE = ALPHA_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_ENFORCER_RECIPE__CONSTRUCTED = ALPHA_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_ENFORCER_RECIPE__PARENT = ALPHA_RECIPE__PARENT;

	/**
	 * The feature id for the '<em><b>Expression</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_ENFORCER_RECIPE__EXPRESSION = ALPHA_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Mapped Indices</b></em>' map.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_ENFORCER_RECIPE__MAPPED_INDICES = ALPHA_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Cache Output</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_ENFORCER_RECIPE__CACHE_OUTPUT = ALPHA_RECIPE_FEATURE_COUNT + 2;

	/**
	 * The number of structural features of the '<em>Expression Enforcer Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_ENFORCER_RECIPE_FEATURE_COUNT = ALPHA_RECIPE_FEATURE_COUNT + 3;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_ENFORCER_RECIPE___GET_ARITY = ALPHA_RECIPE___GET_ARITY;

	/**
	 * The number of operations of the '<em>Expression Enforcer Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_ENFORCER_RECIPE_OPERATION_COUNT = ALPHA_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.CheckRecipeImpl <em>Check Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.CheckRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getCheckRecipe()
	 * @generated
	 */
	int CHECK_RECIPE = 24;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CHECK_RECIPE__TRACE_INFO = EXPRESSION_ENFORCER_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int CHECK_RECIPE__EQUIVALENCE_CLASS_IDS = EXPRESSION_ENFORCER_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CHECK_RECIPE__CACHED_HASH_CODE = EXPRESSION_ENFORCER_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CHECK_RECIPE__CONSTRUCTED = EXPRESSION_ENFORCER_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CHECK_RECIPE__PARENT = EXPRESSION_ENFORCER_RECIPE__PARENT;

	/**
	 * The feature id for the '<em><b>Expression</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CHECK_RECIPE__EXPRESSION = EXPRESSION_ENFORCER_RECIPE__EXPRESSION;

	/**
	 * The feature id for the '<em><b>Mapped Indices</b></em>' map.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CHECK_RECIPE__MAPPED_INDICES = EXPRESSION_ENFORCER_RECIPE__MAPPED_INDICES;

	/**
	 * The feature id for the '<em><b>Cache Output</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CHECK_RECIPE__CACHE_OUTPUT = EXPRESSION_ENFORCER_RECIPE__CACHE_OUTPUT;

	/**
	 * The number of structural features of the '<em>Check Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CHECK_RECIPE_FEATURE_COUNT = EXPRESSION_ENFORCER_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CHECK_RECIPE___GET_ARITY = EXPRESSION_ENFORCER_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Check Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CHECK_RECIPE_OPERATION_COUNT = EXPRESSION_ENFORCER_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.EvalRecipeImpl <em>Eval Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.EvalRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getEvalRecipe()
	 * @generated
	 */
	int EVAL_RECIPE = 25;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EVAL_RECIPE__TRACE_INFO = EXPRESSION_ENFORCER_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int EVAL_RECIPE__EQUIVALENCE_CLASS_IDS = EXPRESSION_ENFORCER_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EVAL_RECIPE__CACHED_HASH_CODE = EXPRESSION_ENFORCER_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EVAL_RECIPE__CONSTRUCTED = EXPRESSION_ENFORCER_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EVAL_RECIPE__PARENT = EXPRESSION_ENFORCER_RECIPE__PARENT;

	/**
	 * The feature id for the '<em><b>Expression</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EVAL_RECIPE__EXPRESSION = EXPRESSION_ENFORCER_RECIPE__EXPRESSION;

	/**
	 * The feature id for the '<em><b>Mapped Indices</b></em>' map.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EVAL_RECIPE__MAPPED_INDICES = EXPRESSION_ENFORCER_RECIPE__MAPPED_INDICES;

	/**
	 * The feature id for the '<em><b>Cache Output</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EVAL_RECIPE__CACHE_OUTPUT = EXPRESSION_ENFORCER_RECIPE__CACHE_OUTPUT;

	/**
	 * The feature id for the '<em><b>Unwinding</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 2.4
	 * @generated
	 * @ordered
	 */
	int EVAL_RECIPE__UNWINDING = EXPRESSION_ENFORCER_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Eval Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EVAL_RECIPE_FEATURE_COUNT = EXPRESSION_ENFORCER_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EVAL_RECIPE___GET_ARITY = EXPRESSION_ENFORCER_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Eval Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EVAL_RECIPE_OPERATION_COUNT = EXPRESSION_ENFORCER_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.IndexerBasedAggregatorRecipeImpl <em>Indexer Based Aggregator Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.IndexerBasedAggregatorRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getIndexerBasedAggregatorRecipe()
	 * @generated
	 */
	int INDEXER_BASED_AGGREGATOR_RECIPE = 26;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEXER_BASED_AGGREGATOR_RECIPE__TRACE_INFO = RETE_NODE_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int INDEXER_BASED_AGGREGATOR_RECIPE__EQUIVALENCE_CLASS_IDS = RETE_NODE_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEXER_BASED_AGGREGATOR_RECIPE__CACHED_HASH_CODE = RETE_NODE_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEXER_BASED_AGGREGATOR_RECIPE__CONSTRUCTED = RETE_NODE_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEXER_BASED_AGGREGATOR_RECIPE__PARENT = RETE_NODE_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Indexer Based Aggregator Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEXER_BASED_AGGREGATOR_RECIPE_FEATURE_COUNT = RETE_NODE_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEXER_BASED_AGGREGATOR_RECIPE___GET_ARITY = RETE_NODE_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Indexer Based Aggregator Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEXER_BASED_AGGREGATOR_RECIPE_OPERATION_COUNT = RETE_NODE_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.CountAggregatorRecipeImpl <em>Count Aggregator Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.CountAggregatorRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getCountAggregatorRecipe()
	 * @generated
	 */
	int COUNT_AGGREGATOR_RECIPE = 27;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COUNT_AGGREGATOR_RECIPE__TRACE_INFO = INDEXER_BASED_AGGREGATOR_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int COUNT_AGGREGATOR_RECIPE__EQUIVALENCE_CLASS_IDS = INDEXER_BASED_AGGREGATOR_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COUNT_AGGREGATOR_RECIPE__CACHED_HASH_CODE = INDEXER_BASED_AGGREGATOR_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COUNT_AGGREGATOR_RECIPE__CONSTRUCTED = INDEXER_BASED_AGGREGATOR_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COUNT_AGGREGATOR_RECIPE__PARENT = INDEXER_BASED_AGGREGATOR_RECIPE__PARENT;

	/**
	 * The number of structural features of the '<em>Count Aggregator Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COUNT_AGGREGATOR_RECIPE_FEATURE_COUNT = INDEXER_BASED_AGGREGATOR_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COUNT_AGGREGATOR_RECIPE___GET_ARITY = INDEXER_BASED_AGGREGATOR_RECIPE___GET_ARITY;

	/**
	 * The number of operations of the '<em>Count Aggregator Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COUNT_AGGREGATOR_RECIPE_OPERATION_COUNT = INDEXER_BASED_AGGREGATOR_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.JoinRecipeImpl <em>Join Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.JoinRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getJoinRecipe()
	 * @generated
	 */
	int JOIN_RECIPE = 28;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int JOIN_RECIPE__TRACE_INFO = BETA_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int JOIN_RECIPE__EQUIVALENCE_CLASS_IDS = BETA_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int JOIN_RECIPE__CACHED_HASH_CODE = BETA_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int JOIN_RECIPE__CONSTRUCTED = BETA_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Left Parent</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int JOIN_RECIPE__LEFT_PARENT = BETA_RECIPE__LEFT_PARENT;

	/**
	 * The feature id for the '<em><b>Right Parent</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int JOIN_RECIPE__RIGHT_PARENT = BETA_RECIPE__RIGHT_PARENT;

	/**
	 * The feature id for the '<em><b>Right Parent Complementary Mask</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int JOIN_RECIPE__RIGHT_PARENT_COMPLEMENTARY_MASK = BETA_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Join Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int JOIN_RECIPE_FEATURE_COUNT = BETA_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int JOIN_RECIPE___GET_ARITY = BETA_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Join Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int JOIN_RECIPE_OPERATION_COUNT = BETA_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.ExistenceJoinRecipeImpl <em>Existence Join Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.ExistenceJoinRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getExistenceJoinRecipe()
	 * @generated
	 */
	int EXISTENCE_JOIN_RECIPE = 29;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXISTENCE_JOIN_RECIPE__TRACE_INFO = BETA_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int EXISTENCE_JOIN_RECIPE__EQUIVALENCE_CLASS_IDS = BETA_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXISTENCE_JOIN_RECIPE__CACHED_HASH_CODE = BETA_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXISTENCE_JOIN_RECIPE__CONSTRUCTED = BETA_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Left Parent</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXISTENCE_JOIN_RECIPE__LEFT_PARENT = BETA_RECIPE__LEFT_PARENT;

	/**
	 * The feature id for the '<em><b>Right Parent</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXISTENCE_JOIN_RECIPE__RIGHT_PARENT = BETA_RECIPE__RIGHT_PARENT;

	/**
	 * The number of structural features of the '<em>Existence Join Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXISTENCE_JOIN_RECIPE_FEATURE_COUNT = BETA_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXISTENCE_JOIN_RECIPE___GET_ARITY = BETA_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Existence Join Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXISTENCE_JOIN_RECIPE_OPERATION_COUNT = BETA_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.SemiJoinRecipeImpl <em>Semi Join Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.SemiJoinRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getSemiJoinRecipe()
	 * @generated
	 */
	int SEMI_JOIN_RECIPE = 30;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SEMI_JOIN_RECIPE__TRACE_INFO = EXISTENCE_JOIN_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int SEMI_JOIN_RECIPE__EQUIVALENCE_CLASS_IDS = EXISTENCE_JOIN_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SEMI_JOIN_RECIPE__CACHED_HASH_CODE = EXISTENCE_JOIN_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SEMI_JOIN_RECIPE__CONSTRUCTED = EXISTENCE_JOIN_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Left Parent</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SEMI_JOIN_RECIPE__LEFT_PARENT = EXISTENCE_JOIN_RECIPE__LEFT_PARENT;

	/**
	 * The feature id for the '<em><b>Right Parent</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SEMI_JOIN_RECIPE__RIGHT_PARENT = EXISTENCE_JOIN_RECIPE__RIGHT_PARENT;

	/**
	 * The number of structural features of the '<em>Semi Join Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SEMI_JOIN_RECIPE_FEATURE_COUNT = EXISTENCE_JOIN_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SEMI_JOIN_RECIPE___GET_ARITY = EXISTENCE_JOIN_RECIPE___GET_ARITY;

	/**
	 * The number of operations of the '<em>Semi Join Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SEMI_JOIN_RECIPE_OPERATION_COUNT = EXISTENCE_JOIN_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.AntiJoinRecipeImpl <em>Anti Join Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.AntiJoinRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getAntiJoinRecipe()
	 * @generated
	 */
	int ANTI_JOIN_RECIPE = 31;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANTI_JOIN_RECIPE__TRACE_INFO = EXISTENCE_JOIN_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int ANTI_JOIN_RECIPE__EQUIVALENCE_CLASS_IDS = EXISTENCE_JOIN_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANTI_JOIN_RECIPE__CACHED_HASH_CODE = EXISTENCE_JOIN_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANTI_JOIN_RECIPE__CONSTRUCTED = EXISTENCE_JOIN_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Left Parent</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANTI_JOIN_RECIPE__LEFT_PARENT = EXISTENCE_JOIN_RECIPE__LEFT_PARENT;

	/**
	 * The feature id for the '<em><b>Right Parent</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANTI_JOIN_RECIPE__RIGHT_PARENT = EXISTENCE_JOIN_RECIPE__RIGHT_PARENT;

	/**
	 * The number of structural features of the '<em>Anti Join Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANTI_JOIN_RECIPE_FEATURE_COUNT = EXISTENCE_JOIN_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANTI_JOIN_RECIPE___GET_ARITY = EXISTENCE_JOIN_RECIPE___GET_ARITY;

	/**
	 * The number of operations of the '<em>Anti Join Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANTI_JOIN_RECIPE_OPERATION_COUNT = EXISTENCE_JOIN_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.InputFilterRecipeImpl <em>Input Filter Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.InputFilterRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getInputFilterRecipe()
	 * @generated
	 */
	int INPUT_FILTER_RECIPE = 32;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_FILTER_RECIPE__TRACE_INFO = FILTER_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int INPUT_FILTER_RECIPE__EQUIVALENCE_CLASS_IDS = FILTER_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_FILTER_RECIPE__CACHED_HASH_CODE = FILTER_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_FILTER_RECIPE__CONSTRUCTED = FILTER_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_FILTER_RECIPE__PARENT = FILTER_RECIPE__PARENT;

	/**
	 * The feature id for the '<em><b>Input Key</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_FILTER_RECIPE__INPUT_KEY = FILTER_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Key ID</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_FILTER_RECIPE__KEY_ID = FILTER_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Mask</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_FILTER_RECIPE__MASK = FILTER_RECIPE_FEATURE_COUNT + 2;

	/**
	 * The number of structural features of the '<em>Input Filter Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_FILTER_RECIPE_FEATURE_COUNT = FILTER_RECIPE_FEATURE_COUNT + 3;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_FILTER_RECIPE___GET_ARITY = FILTER_RECIPE___GET_ARITY;

	/**
	 * The number of operations of the '<em>Input Filter Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INPUT_FILTER_RECIPE_OPERATION_COUNT = FILTER_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.SingleColumnAggregatorRecipeImpl <em>Single Column Aggregator Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.SingleColumnAggregatorRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getSingleColumnAggregatorRecipe()
	 * @generated
	 */
	int SINGLE_COLUMN_AGGREGATOR_RECIPE = 33;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_COLUMN_AGGREGATOR_RECIPE__TRACE_INFO = ALPHA_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int SINGLE_COLUMN_AGGREGATOR_RECIPE__EQUIVALENCE_CLASS_IDS = ALPHA_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_COLUMN_AGGREGATOR_RECIPE__CACHED_HASH_CODE = ALPHA_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_COLUMN_AGGREGATOR_RECIPE__CONSTRUCTED = ALPHA_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_COLUMN_AGGREGATOR_RECIPE__PARENT = ALPHA_RECIPE__PARENT;

	/**
	 * The feature id for the '<em><b>Delete Rederive Evaluation</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_COLUMN_AGGREGATOR_RECIPE__DELETE_REDERIVE_EVALUATION = ALPHA_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Optional Monotonicity Info</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_COLUMN_AGGREGATOR_RECIPE__OPTIONAL_MONOTONICITY_INFO = ALPHA_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Multiset Aggregation Operator</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_COLUMN_AGGREGATOR_RECIPE__MULTISET_AGGREGATION_OPERATOR = ALPHA_RECIPE_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Aggregable Index</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_COLUMN_AGGREGATOR_RECIPE__AGGREGABLE_INDEX = ALPHA_RECIPE_FEATURE_COUNT + 3;

	/**
	 * The feature id for the '<em><b>Group By Mask</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_COLUMN_AGGREGATOR_RECIPE__GROUP_BY_MASK = ALPHA_RECIPE_FEATURE_COUNT + 4;

	/**
	 * The number of structural features of the '<em>Single Column Aggregator Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_COLUMN_AGGREGATOR_RECIPE_FEATURE_COUNT = ALPHA_RECIPE_FEATURE_COUNT + 5;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_COLUMN_AGGREGATOR_RECIPE___GET_ARITY = ALPHA_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Single Column Aggregator Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_COLUMN_AGGREGATOR_RECIPE_OPERATION_COUNT = ALPHA_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.DiscriminatorDispatcherRecipeImpl <em>Discriminator Dispatcher Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.DiscriminatorDispatcherRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getDiscriminatorDispatcherRecipe()
	 * @generated
	 */
	int DISCRIMINATOR_DISPATCHER_RECIPE = 34;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_DISPATCHER_RECIPE__TRACE_INFO = SINGLE_PARENT_NODE_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_DISPATCHER_RECIPE__EQUIVALENCE_CLASS_IDS = SINGLE_PARENT_NODE_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_DISPATCHER_RECIPE__CACHED_HASH_CODE = SINGLE_PARENT_NODE_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_DISPATCHER_RECIPE__CONSTRUCTED = SINGLE_PARENT_NODE_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_DISPATCHER_RECIPE__PARENT = SINGLE_PARENT_NODE_RECIPE__PARENT;

	/**
	 * The feature id for the '<em><b>Discrimination Column Index</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_DISPATCHER_RECIPE__DISCRIMINATION_COLUMN_INDEX = SINGLE_PARENT_NODE_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Discriminator Dispatcher Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_DISPATCHER_RECIPE_FEATURE_COUNT = SINGLE_PARENT_NODE_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_DISPATCHER_RECIPE___GET_ARITY = SINGLE_PARENT_NODE_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Discriminator Dispatcher Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_DISPATCHER_RECIPE_OPERATION_COUNT = SINGLE_PARENT_NODE_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.DiscriminatorBucketRecipeImpl <em>Discriminator Bucket Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.DiscriminatorBucketRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getDiscriminatorBucketRecipe()
	 * @generated
	 */
	int DISCRIMINATOR_BUCKET_RECIPE = 35;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_BUCKET_RECIPE__TRACE_INFO = SINGLE_PARENT_NODE_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_BUCKET_RECIPE__EQUIVALENCE_CLASS_IDS = SINGLE_PARENT_NODE_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_BUCKET_RECIPE__CACHED_HASH_CODE = SINGLE_PARENT_NODE_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_BUCKET_RECIPE__CONSTRUCTED = SINGLE_PARENT_NODE_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_BUCKET_RECIPE__PARENT = SINGLE_PARENT_NODE_RECIPE__PARENT;

	/**
	 * The feature id for the '<em><b>Bucket Key</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_BUCKET_RECIPE__BUCKET_KEY = SINGLE_PARENT_NODE_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Discriminator Bucket Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_BUCKET_RECIPE_FEATURE_COUNT = SINGLE_PARENT_NODE_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_BUCKET_RECIPE___GET_ARITY = SINGLE_PARENT_NODE_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Discriminator Bucket Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DISCRIMINATOR_BUCKET_RECIPE_OPERATION_COUNT = SINGLE_PARENT_NODE_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.RederivableNodeRecipeImpl <em>Rederivable Node Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.RederivableNodeRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getRederivableNodeRecipe()
	 * @generated
	 */
	int REDERIVABLE_NODE_RECIPE = 36;

	/**
	 * The feature id for the '<em><b>Delete Rederive Evaluation</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REDERIVABLE_NODE_RECIPE__DELETE_REDERIVE_EVALUATION = 0;

	/**
	 * The feature id for the '<em><b>Optional Monotonicity Info</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REDERIVABLE_NODE_RECIPE__OPTIONAL_MONOTONICITY_INFO = 1;

	/**
	 * The number of structural features of the '<em>Rederivable Node Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REDERIVABLE_NODE_RECIPE_FEATURE_COUNT = 2;

	/**
	 * The number of operations of the '<em>Rederivable Node Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REDERIVABLE_NODE_RECIPE_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.RelationEvaluationRecipeImpl <em>Relation Evaluation Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.RelationEvaluationRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getRelationEvaluationRecipe()
	 * @since 2.8
	 * @generated
	 */
	int RELATION_EVALUATION_RECIPE = 37;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RELATION_EVALUATION_RECIPE__TRACE_INFO = MULTI_PARENT_NODE_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int RELATION_EVALUATION_RECIPE__EQUIVALENCE_CLASS_IDS = MULTI_PARENT_NODE_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RELATION_EVALUATION_RECIPE__CACHED_HASH_CODE = MULTI_PARENT_NODE_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RELATION_EVALUATION_RECIPE__CONSTRUCTED = MULTI_PARENT_NODE_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parents</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RELATION_EVALUATION_RECIPE__PARENTS = MULTI_PARENT_NODE_RECIPE__PARENTS;

	/**
	 * The feature id for the '<em><b>Evaluator</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 2.8
	 * @generated
	 * @ordered
	 */
	int RELATION_EVALUATION_RECIPE__EVALUATOR = MULTI_PARENT_NODE_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Relation Evaluation Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 2.8
	 * @generated
	 * @ordered
	 */
	int RELATION_EVALUATION_RECIPE_FEATURE_COUNT = MULTI_PARENT_NODE_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RELATION_EVALUATION_RECIPE___GET_ARITY = MULTI_PARENT_NODE_RECIPE___GET_ARITY;

	/**
	 * The number of operations of the '<em>Relation Evaluation Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 2.8
	 * @generated
	 * @ordered
	 */
	int RELATION_EVALUATION_RECIPE_OPERATION_COUNT = MULTI_PARENT_NODE_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.RepresentativeElectionRecipeImpl <em>Representative Election Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.RepresentativeElectionRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getRepresentativeElectionRecipe()
	 * @generated
	 */
	int REPRESENTATIVE_ELECTION_RECIPE = 38;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REPRESENTATIVE_ELECTION_RECIPE__TRACE_INFO = ALPHA_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int REPRESENTATIVE_ELECTION_RECIPE__EQUIVALENCE_CLASS_IDS = ALPHA_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REPRESENTATIVE_ELECTION_RECIPE__CACHED_HASH_CODE = ALPHA_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REPRESENTATIVE_ELECTION_RECIPE__CONSTRUCTED = ALPHA_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REPRESENTATIVE_ELECTION_RECIPE__PARENT = ALPHA_RECIPE__PARENT;

	/**
	 * The feature id for the '<em><b>Connectivity</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REPRESENTATIVE_ELECTION_RECIPE__CONNECTIVITY = ALPHA_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Representative Election Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REPRESENTATIVE_ELECTION_RECIPE_FEATURE_COUNT = ALPHA_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REPRESENTATIVE_ELECTION_RECIPE___GET_ARITY = ALPHA_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Representative Election Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REPRESENTATIVE_ELECTION_RECIPE_OPERATION_COUNT = ALPHA_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.OuterJoinNodeRecipeImpl <em>Outer Join Node Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.OuterJoinNodeRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getOuterJoinNodeRecipe()
	 * @generated
	 */
	int OUTER_JOIN_NODE_RECIPE = 39;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_NODE_RECIPE__TRACE_INFO = RETE_NODE_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_NODE_RECIPE__EQUIVALENCE_CLASS_IDS = RETE_NODE_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_NODE_RECIPE__CACHED_HASH_CODE = RETE_NODE_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_NODE_RECIPE__CONSTRUCTED = RETE_NODE_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_NODE_RECIPE__PARENT = RETE_NODE_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Default Value</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_NODE_RECIPE__DEFAULT_VALUE = RETE_NODE_RECIPE_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Outer Join Node Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_NODE_RECIPE_FEATURE_COUNT = RETE_NODE_RECIPE_FEATURE_COUNT + 2;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_NODE_RECIPE___GET_ARITY = RETE_NODE_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The number of operations of the '<em>Outer Join Node Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_NODE_RECIPE_OPERATION_COUNT = RETE_NODE_RECIPE_OPERATION_COUNT + 1;

	/**
	 * The meta object id for the '{@link tools.refinery.interpreter.rete.recipes.impl.OuterJoinIndexerRecipeImpl <em>Outer Join Indexer Recipe</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.rete.recipes.impl.OuterJoinIndexerRecipeImpl
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getOuterJoinIndexerRecipe()
	 * @generated
	 */
	int OUTER_JOIN_INDEXER_RECIPE = 40;

	/**
	 * The feature id for the '<em><b>Trace Info</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_INDEXER_RECIPE__TRACE_INFO = INDEXER_RECIPE__TRACE_INFO;

	/**
	 * The feature id for the '<em><b>Equivalence Class IDs</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_INDEXER_RECIPE__EQUIVALENCE_CLASS_IDS = INDEXER_RECIPE__EQUIVALENCE_CLASS_IDS;

	/**
	 * The feature id for the '<em><b>Cached Hash Code</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_INDEXER_RECIPE__CACHED_HASH_CODE = INDEXER_RECIPE__CACHED_HASH_CODE;

	/**
	 * The feature id for the '<em><b>Constructed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_INDEXER_RECIPE__CONSTRUCTED = INDEXER_RECIPE__CONSTRUCTED;

	/**
	 * The feature id for the '<em><b>Parent</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_INDEXER_RECIPE__PARENT = INDEXER_RECIPE__PARENT;

	/**
	 * The feature id for the '<em><b>Mask</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_INDEXER_RECIPE__MASK = INDEXER_RECIPE__MASK;

	/**
	 * The number of structural features of the '<em>Outer Join Indexer Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_INDEXER_RECIPE_FEATURE_COUNT = INDEXER_RECIPE_FEATURE_COUNT + 0;

	/**
	 * The operation id for the '<em>Get Arity</em>' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_INDEXER_RECIPE___GET_ARITY = INDEXER_RECIPE___GET_ARITY;

	/**
	 * The number of operations of the '<em>Outer Join Indexer Recipe</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OUTER_JOIN_INDEXER_RECIPE_OPERATION_COUNT = INDEXER_RECIPE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '<em>Index</em>' data type.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see java.lang.Integer
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getIndex()
	 * @generated
	 */
	int INDEX = 41;

	/**
	 * The meta object id for the '<em>Aggregation Operator</em>' data type.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.matchers.psystem.aggregations.IMultisetAggregationOperator
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getAggregationOperator()
	 * @generated
	 */
	int AGGREGATION_OPERATOR = 42;

	/**
	 * The meta object id for the '<em>Connectivity</em>' data type.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.interpreter.matchers.psystem.basicenumerables.Connectivity
	 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getConnectivity()
	 * @generated
	 */
	int CONNECTIVITY = 43;


	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.ReteRecipe <em>Rete Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Rete Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ReteRecipe
	 * @generated
	 */
	EClass getReteRecipe();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.interpreter.rete.recipes.ReteRecipe#getRecipeNodes <em>Recipe Nodes</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Recipe Nodes</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ReteRecipe#getRecipeNodes()
	 * @see #getReteRecipe()
	 * @generated
	 */
	EReference getReteRecipe_RecipeNodes();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.ReteNodeRecipe <em>Rete Node Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Rete Node Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ReteNodeRecipe
	 * @generated
	 */
	EClass getReteNodeRecipe();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.ReteNodeRecipe#getTraceInfo <em>Trace Info</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Trace Info</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ReteNodeRecipe#getTraceInfo()
	 * @see #getReteNodeRecipe()
	 * @generated
	 */
	EAttribute getReteNodeRecipe_TraceInfo();

	/**
	 * Returns the meta object for the attribute list '{@link tools.refinery.interpreter.rete.recipes.ReteNodeRecipe#getEquivalenceClassIDs <em>Equivalence Class IDs</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute list '<em>Equivalence Class IDs</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ReteNodeRecipe#getEquivalenceClassIDs()
	 * @see #getReteNodeRecipe()
	 * @since 1.3
	 * @generated
	 */
	EAttribute getReteNodeRecipe_EquivalenceClassIDs();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.ReteNodeRecipe#getCachedHashCode <em>Cached Hash Code</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Cached Hash Code</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ReteNodeRecipe#getCachedHashCode()
	 * @see #getReteNodeRecipe()
	 * @generated
	 */
	EAttribute getReteNodeRecipe_CachedHashCode();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.ReteNodeRecipe#isConstructed <em>Constructed</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Constructed</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ReteNodeRecipe#isConstructed()
	 * @see #getReteNodeRecipe()
	 * @generated
	 */
	EAttribute getReteNodeRecipe_Constructed();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.ReteNodeRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.ReteNodeRecipe#getArity()
	 * @generated
	 */
	EOperation getReteNodeRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.SingleParentNodeRecipe <em>Single Parent Node Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Single Parent Node Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.SingleParentNodeRecipe
	 * @generated
	 */
	EClass getSingleParentNodeRecipe();

	/**
	 * Returns the meta object for the reference '{@link tools.refinery.interpreter.rete.recipes.SingleParentNodeRecipe#getParent <em>Parent</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Parent</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.SingleParentNodeRecipe#getParent()
	 * @see #getSingleParentNodeRecipe()
	 * @generated
	 */
	EReference getSingleParentNodeRecipe_Parent();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.AlphaRecipe <em>Alpha Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Alpha Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.AlphaRecipe
	 * @generated
	 */
	EClass getAlphaRecipe();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.MultiParentNodeRecipe <em>Multi Parent Node Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Multi Parent Node Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.MultiParentNodeRecipe
	 * @generated
	 */
	EClass getMultiParentNodeRecipe();

	/**
	 * Returns the meta object for the reference list '{@link tools.refinery.interpreter.rete.recipes.MultiParentNodeRecipe#getParents <em>Parents</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Parents</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.MultiParentNodeRecipe#getParents()
	 * @see #getMultiParentNodeRecipe()
	 * @generated
	 */
	EReference getMultiParentNodeRecipe_Parents();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.MultiParentNodeRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.MultiParentNodeRecipe#getArity()
	 * @generated
	 */
	EOperation getMultiParentNodeRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.MonotonicityInfo <em>Monotonicity Info</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Monotonicity Info</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.MonotonicityInfo
	 * @generated
	 */
	EClass getMonotonicityInfo();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.interpreter.rete.recipes.MonotonicityInfo#getCoreMask <em>Core Mask</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Core Mask</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.MonotonicityInfo#getCoreMask()
	 * @see #getMonotonicityInfo()
	 * @generated
	 */
	EReference getMonotonicityInfo_CoreMask();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.interpreter.rete.recipes.MonotonicityInfo#getPosetMask <em>Poset Mask</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Poset Mask</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.MonotonicityInfo#getPosetMask()
	 * @see #getMonotonicityInfo()
	 * @generated
	 */
	EReference getMonotonicityInfo_PosetMask();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.MonotonicityInfo#getPosetComparator <em>Poset Comparator</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Poset Comparator</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.MonotonicityInfo#getPosetComparator()
	 * @see #getMonotonicityInfo()
	 * @generated
	 */
	EAttribute getMonotonicityInfo_PosetComparator();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.UniquenessEnforcerRecipe <em>Uniqueness Enforcer Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Uniqueness Enforcer Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.UniquenessEnforcerRecipe
	 * @generated
	 */
	EClass getUniquenessEnforcerRecipe();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.ProductionRecipe <em>Production Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Production Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ProductionRecipe
	 * @generated
	 */
	EClass getProductionRecipe();

	/**
	 * Returns the meta object for the map '{@link tools.refinery.interpreter.rete.recipes.ProductionRecipe#getMappedIndices <em>Mapped Indices</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the map '<em>Mapped Indices</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ProductionRecipe#getMappedIndices()
	 * @see #getProductionRecipe()
	 * @generated
	 */
	EReference getProductionRecipe_MappedIndices();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.ProductionRecipe#getPattern <em>Pattern</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Pattern</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ProductionRecipe#getPattern()
	 * @see #getProductionRecipe()
	 * @generated
	 */
	EAttribute getProductionRecipe_Pattern();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.ProductionRecipe#getPatternFQN <em>Pattern FQN</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Pattern FQN</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ProductionRecipe#getPatternFQN()
	 * @see #getProductionRecipe()
	 * @generated
	 */
	EAttribute getProductionRecipe_PatternFQN();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.ProductionRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.ProductionRecipe#getArity()
	 * @generated
	 */
	EOperation getProductionRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.IndexerRecipe <em>Indexer Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Indexer Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.IndexerRecipe
	 * @generated
	 */
	EClass getIndexerRecipe();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.interpreter.rete.recipes.IndexerRecipe#getMask <em>Mask</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Mask</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.IndexerRecipe#getMask()
	 * @see #getIndexerRecipe()
	 * @generated
	 */
	EReference getIndexerRecipe_Mask();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.IndexerRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.IndexerRecipe#getArity()
	 * @generated
	 */
	EOperation getIndexerRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.ProjectionIndexerRecipe <em>Projection Indexer Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Projection Indexer Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ProjectionIndexerRecipe
	 * @generated
	 */
	EClass getProjectionIndexerRecipe();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.AggregatorIndexerRecipe <em>Aggregator Indexer Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Aggregator Indexer Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.AggregatorIndexerRecipe
	 * @generated
	 */
	EClass getAggregatorIndexerRecipe();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.BetaRecipe <em>Beta Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Beta Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.BetaRecipe
	 * @generated
	 */
	EClass getBetaRecipe();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.interpreter.rete.recipes.BetaRecipe#getLeftParent <em>Left Parent</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left Parent</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.BetaRecipe#getLeftParent()
	 * @see #getBetaRecipe()
	 * @generated
	 */
	EReference getBetaRecipe_LeftParent();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.interpreter.rete.recipes.BetaRecipe#getRightParent <em>Right Parent</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right Parent</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.BetaRecipe#getRightParent()
	 * @see #getBetaRecipe()
	 * @generated
	 */
	EReference getBetaRecipe_RightParent();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.Mask <em>Mask</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Mask</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.Mask
	 * @generated
	 */
	EClass getMask();

	/**
	 * Returns the meta object for the attribute list '{@link tools.refinery.interpreter.rete.recipes.Mask#getSourceIndices <em>Source Indices</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute list '<em>Source Indices</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.Mask#getSourceIndices()
	 * @see #getMask()
	 * @generated
	 */
	EAttribute getMask_SourceIndices();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.Mask#getSourceArity <em>Source Arity</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Source Arity</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.Mask#getSourceArity()
	 * @see #getMask()
	 * @generated
	 */
	EAttribute getMask_SourceArity();

	/**
	 * Returns the meta object for class '{@link java.util.Map.Entry <em>String Index Map Entry</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>String Index Map Entry</em>'.
	 * @see java.util.Map.Entry
	 * @model keyUnique="false" keyDataType="org.eclipse.emf.ecore.EString"
	 *        valueUnique="false" valueDataType="tools.refinery.interpreter.rete.recipes.Index"
	 * @generated
	 */
	EClass getStringIndexMapEntry();

	/**
	 * Returns the meta object for the attribute '{@link java.util.Map.Entry <em>Key</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Key</em>'.
	 * @see java.util.Map.Entry
	 * @see #getStringIndexMapEntry()
	 * @generated
	 */
	EAttribute getStringIndexMapEntry_Key();

	/**
	 * Returns the meta object for the attribute '{@link java.util.Map.Entry <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Value</em>'.
	 * @see java.util.Map.Entry
	 * @see #getStringIndexMapEntry()
	 * @generated
	 */
	EAttribute getStringIndexMapEntry_Value();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.InputRecipe <em>Input Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Input Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.InputRecipe
	 * @generated
	 */
	EClass getInputRecipe();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.InputRecipe#getInputKey <em>Input Key</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Input Key</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.InputRecipe#getInputKey()
	 * @see #getInputRecipe()
	 * @generated
	 */
	EAttribute getInputRecipe_InputKey();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.InputRecipe#getKeyID <em>Key ID</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Key ID</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.InputRecipe#getKeyID()
	 * @see #getInputRecipe()
	 * @generated
	 */
	EAttribute getInputRecipe_KeyID();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.InputRecipe#getKeyArity <em>Key Arity</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Key Arity</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.InputRecipe#getKeyArity()
	 * @see #getInputRecipe()
	 * @generated
	 */
	EAttribute getInputRecipe_KeyArity();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.InputRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.InputRecipe#getArity()
	 * @generated
	 */
	EOperation getInputRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.ConstantRecipe <em>Constant Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Constant Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ConstantRecipe
	 * @generated
	 */
	EClass getConstantRecipe();

	/**
	 * Returns the meta object for the attribute list '{@link tools.refinery.interpreter.rete.recipes.ConstantRecipe#getConstantValues <em>Constant Values</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute list '<em>Constant Values</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ConstantRecipe#getConstantValues()
	 * @see #getConstantRecipe()
	 * @generated
	 */
	EAttribute getConstantRecipe_ConstantValues();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.ConstantRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.ConstantRecipe#getArity()
	 * @generated
	 */
	EOperation getConstantRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.TransitiveClosureRecipe <em>Transitive Closure Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Transitive Closure Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.TransitiveClosureRecipe
	 * @generated
	 */
	EClass getTransitiveClosureRecipe();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.TransitiveClosureRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.TransitiveClosureRecipe#getArity()
	 * @generated
	 */
	EOperation getTransitiveClosureRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.FilterRecipe <em>Filter Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Filter Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.FilterRecipe
	 * @generated
	 */
	EClass getFilterRecipe();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.FilterRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.FilterRecipe#getArity()
	 * @generated
	 */
	EOperation getFilterRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.InequalityFilterRecipe <em>Inequality Filter Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Inequality Filter Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.InequalityFilterRecipe
	 * @generated
	 */
	EClass getInequalityFilterRecipe();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.InequalityFilterRecipe#getSubject <em>Subject</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Subject</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.InequalityFilterRecipe#getSubject()
	 * @see #getInequalityFilterRecipe()
	 * @generated
	 */
	EAttribute getInequalityFilterRecipe_Subject();

	/**
	 * Returns the meta object for the attribute list '{@link tools.refinery.interpreter.rete.recipes.InequalityFilterRecipe#getInequals <em>Inequals</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute list '<em>Inequals</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.InequalityFilterRecipe#getInequals()
	 * @see #getInequalityFilterRecipe()
	 * @generated
	 */
	EAttribute getInequalityFilterRecipe_Inequals();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.EqualityFilterRecipe <em>Equality Filter Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Equality Filter Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.EqualityFilterRecipe
	 * @generated
	 */
	EClass getEqualityFilterRecipe();

	/**
	 * Returns the meta object for the attribute list '{@link tools.refinery.interpreter.rete.recipes.EqualityFilterRecipe#getIndices <em>Indices</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute list '<em>Indices</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.EqualityFilterRecipe#getIndices()
	 * @see #getEqualityFilterRecipe()
	 * @generated
	 */
	EAttribute getEqualityFilterRecipe_Indices();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.TransparentRecipe <em>Transparent Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Transparent Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.TransparentRecipe
	 * @generated
	 */
	EClass getTransparentRecipe();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.TrimmerRecipe <em>Trimmer Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Trimmer Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.TrimmerRecipe
	 * @generated
	 */
	EClass getTrimmerRecipe();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.interpreter.rete.recipes.TrimmerRecipe#getMask <em>Mask</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Mask</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.TrimmerRecipe#getMask()
	 * @see #getTrimmerRecipe()
	 * @generated
	 */
	EReference getTrimmerRecipe_Mask();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.TrimmerRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.TrimmerRecipe#getArity()
	 * @generated
	 */
	EOperation getTrimmerRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.ExpressionDefinition <em>Expression Definition</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Expression Definition</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ExpressionDefinition
	 * @generated
	 */
	EClass getExpressionDefinition();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.ExpressionDefinition#getEvaluator <em>Evaluator</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Evaluator</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ExpressionDefinition#getEvaluator()
	 * @see #getExpressionDefinition()
	 * @generated
	 */
	EAttribute getExpressionDefinition_Evaluator();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.ExpressionEnforcerRecipe <em>Expression Enforcer Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Expression Enforcer Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ExpressionEnforcerRecipe
	 * @generated
	 */
	EClass getExpressionEnforcerRecipe();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.interpreter.rete.recipes.ExpressionEnforcerRecipe#getExpression <em>Expression</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Expression</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ExpressionEnforcerRecipe#getExpression()
	 * @see #getExpressionEnforcerRecipe()
	 * @generated
	 */
	EReference getExpressionEnforcerRecipe_Expression();

	/**
	 * Returns the meta object for the map '{@link tools.refinery.interpreter.rete.recipes.ExpressionEnforcerRecipe#getMappedIndices <em>Mapped Indices</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the map '<em>Mapped Indices</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ExpressionEnforcerRecipe#getMappedIndices()
	 * @see #getExpressionEnforcerRecipe()
	 * @generated
	 */
	EReference getExpressionEnforcerRecipe_MappedIndices();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.ExpressionEnforcerRecipe#isCacheOutput <em>Cache Output</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Cache Output</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ExpressionEnforcerRecipe#isCacheOutput()
	 * @see #getExpressionEnforcerRecipe()
	 * @generated
	 */
	EAttribute getExpressionEnforcerRecipe_CacheOutput();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.CheckRecipe <em>Check Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Check Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.CheckRecipe
	 * @generated
	 */
	EClass getCheckRecipe();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.CheckRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.CheckRecipe#getArity()
	 * @generated
	 */
	EOperation getCheckRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.EvalRecipe <em>Eval Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Eval Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.EvalRecipe
	 * @generated
	 */
	EClass getEvalRecipe();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.EvalRecipe#isUnwinding <em>Unwinding</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Unwinding</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.EvalRecipe#isUnwinding()
	 * @see #getEvalRecipe()
	 * @since 2.4
	 * @generated
	 */
	EAttribute getEvalRecipe_Unwinding();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.EvalRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.EvalRecipe#getArity()
	 * @generated
	 */
	EOperation getEvalRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.IndexerBasedAggregatorRecipe <em>Indexer Based Aggregator Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Indexer Based Aggregator Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.IndexerBasedAggregatorRecipe
	 * @generated
	 */
	EClass getIndexerBasedAggregatorRecipe();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.interpreter.rete.recipes.IndexerBasedAggregatorRecipe#getParent <em>Parent</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Parent</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.IndexerBasedAggregatorRecipe#getParent()
	 * @see #getIndexerBasedAggregatorRecipe()
	 * @generated
	 */
	EReference getIndexerBasedAggregatorRecipe_Parent();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.IndexerBasedAggregatorRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.IndexerBasedAggregatorRecipe#getArity()
	 * @generated
	 */
	EOperation getIndexerBasedAggregatorRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.CountAggregatorRecipe <em>Count Aggregator Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Count Aggregator Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.CountAggregatorRecipe
	 * @generated
	 */
	EClass getCountAggregatorRecipe();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.JoinRecipe <em>Join Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Join Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.JoinRecipe
	 * @generated
	 */
	EClass getJoinRecipe();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.interpreter.rete.recipes.JoinRecipe#getRightParentComplementaryMask <em>Right Parent Complementary Mask</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right Parent Complementary Mask</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.JoinRecipe#getRightParentComplementaryMask()
	 * @see #getJoinRecipe()
	 * @generated
	 */
	EReference getJoinRecipe_RightParentComplementaryMask();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.JoinRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.JoinRecipe#getArity()
	 * @generated
	 */
	EOperation getJoinRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.ExistenceJoinRecipe <em>Existence Join Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Existence Join Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.ExistenceJoinRecipe
	 * @generated
	 */
	EClass getExistenceJoinRecipe();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.ExistenceJoinRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.ExistenceJoinRecipe#getArity()
	 * @generated
	 */
	EOperation getExistenceJoinRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.SemiJoinRecipe <em>Semi Join Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Semi Join Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.SemiJoinRecipe
	 * @generated
	 */
	EClass getSemiJoinRecipe();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.AntiJoinRecipe <em>Anti Join Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Anti Join Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.AntiJoinRecipe
	 * @generated
	 */
	EClass getAntiJoinRecipe();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.InputFilterRecipe <em>Input Filter Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Input Filter Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.InputFilterRecipe
	 * @generated
	 */
	EClass getInputFilterRecipe();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.InputFilterRecipe#getInputKey <em>Input Key</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Input Key</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.InputFilterRecipe#getInputKey()
	 * @see #getInputFilterRecipe()
	 * @generated
	 */
	EAttribute getInputFilterRecipe_InputKey();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.InputFilterRecipe#getKeyID <em>Key ID</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Key ID</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.InputFilterRecipe#getKeyID()
	 * @see #getInputFilterRecipe()
	 * @generated
	 */
	EAttribute getInputFilterRecipe_KeyID();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.interpreter.rete.recipes.InputFilterRecipe#getMask <em>Mask</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Mask</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.InputFilterRecipe#getMask()
	 * @see #getInputFilterRecipe()
	 * @generated
	 */
	EReference getInputFilterRecipe_Mask();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe <em>Single Column Aggregator Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Single Column Aggregator Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe
	 * @generated
	 */
	EClass getSingleColumnAggregatorRecipe();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe#getMultisetAggregationOperator <em>Multiset Aggregation Operator</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Multiset Aggregation Operator</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe#getMultisetAggregationOperator()
	 * @see #getSingleColumnAggregatorRecipe()
	 * @generated
	 */
	EAttribute getSingleColumnAggregatorRecipe_MultisetAggregationOperator();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe#getAggregableIndex <em>Aggregable Index</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Aggregable Index</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe#getAggregableIndex()
	 * @see #getSingleColumnAggregatorRecipe()
	 * @generated
	 */
	EAttribute getSingleColumnAggregatorRecipe_AggregableIndex();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe#getGroupByMask <em>Group By Mask</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Group By Mask</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe#getGroupByMask()
	 * @see #getSingleColumnAggregatorRecipe()
	 * @generated
	 */
	EReference getSingleColumnAggregatorRecipe_GroupByMask();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe#getArity()
	 * @generated
	 */
	EOperation getSingleColumnAggregatorRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.DiscriminatorDispatcherRecipe <em>Discriminator Dispatcher Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Discriminator Dispatcher Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.DiscriminatorDispatcherRecipe
	 * @generated
	 */
	EClass getDiscriminatorDispatcherRecipe();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.DiscriminatorDispatcherRecipe#getDiscriminationColumnIndex <em>Discrimination Column Index</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Discrimination Column Index</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.DiscriminatorDispatcherRecipe#getDiscriminationColumnIndex()
	 * @see #getDiscriminatorDispatcherRecipe()
	 * @generated
	 */
	EAttribute getDiscriminatorDispatcherRecipe_DiscriminationColumnIndex();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.DiscriminatorDispatcherRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.DiscriminatorDispatcherRecipe#getArity()
	 * @generated
	 */
	EOperation getDiscriminatorDispatcherRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.DiscriminatorBucketRecipe <em>Discriminator Bucket Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Discriminator Bucket Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.DiscriminatorBucketRecipe
	 * @generated
	 */
	EClass getDiscriminatorBucketRecipe();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.DiscriminatorBucketRecipe#getBucketKey <em>Bucket Key</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Bucket Key</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.DiscriminatorBucketRecipe#getBucketKey()
	 * @see #getDiscriminatorBucketRecipe()
	 * @generated
	 */
	EAttribute getDiscriminatorBucketRecipe_BucketKey();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.DiscriminatorBucketRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.DiscriminatorBucketRecipe#getArity()
	 * @generated
	 */
	EOperation getDiscriminatorBucketRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.RederivableNodeRecipe <em>Rederivable Node Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Rederivable Node Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.RederivableNodeRecipe
	 * @generated
	 */
	EClass getRederivableNodeRecipe();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.RederivableNodeRecipe#isDeleteRederiveEvaluation <em>Delete Rederive Evaluation</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Delete Rederive Evaluation</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.RederivableNodeRecipe#isDeleteRederiveEvaluation()
	 * @see #getRederivableNodeRecipe()
	 * @generated
	 */
	EAttribute getRederivableNodeRecipe_DeleteRederiveEvaluation();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.interpreter.rete.recipes.RederivableNodeRecipe#getOptionalMonotonicityInfo <em>Optional Monotonicity Info</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Optional Monotonicity Info</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.RederivableNodeRecipe#getOptionalMonotonicityInfo()
	 * @see #getRederivableNodeRecipe()
	 * @generated
	 */
	EReference getRederivableNodeRecipe_OptionalMonotonicityInfo();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.RelationEvaluationRecipe <em>Relation Evaluation Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Relation Evaluation Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.RelationEvaluationRecipe
	 * @since 2.8
	 * @generated
	 */
	EClass getRelationEvaluationRecipe();

	/**
	 * Returns the meta object for the reference '{@link tools.refinery.interpreter.rete.recipes.RelationEvaluationRecipe#getEvaluator <em>Evaluator</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Evaluator</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.RelationEvaluationRecipe#getEvaluator()
	 * @see #getRelationEvaluationRecipe()
	 * @since 2.8
	 * @generated
	 */
	EReference getRelationEvaluationRecipe_Evaluator();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.RepresentativeElectionRecipe <em>Representative Election Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Representative Election Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.RepresentativeElectionRecipe
	 * @generated
	 */
	EClass getRepresentativeElectionRecipe();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.RepresentativeElectionRecipe#getConnectivity <em>Connectivity</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Connectivity</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.RepresentativeElectionRecipe#getConnectivity()
	 * @see #getRepresentativeElectionRecipe()
	 * @generated
	 */
	EAttribute getRepresentativeElectionRecipe_Connectivity();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.RepresentativeElectionRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.RepresentativeElectionRecipe#getArity()
	 * @generated
	 */
	EOperation getRepresentativeElectionRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.OuterJoinNodeRecipe <em>Outer Join Node Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Outer Join Node Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.OuterJoinNodeRecipe
	 * @generated
	 */
	EClass getOuterJoinNodeRecipe();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.interpreter.rete.recipes.OuterJoinNodeRecipe#getParent <em>Parent</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Parent</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.OuterJoinNodeRecipe#getParent()
	 * @see #getOuterJoinNodeRecipe()
	 * @generated
	 */
	EReference getOuterJoinNodeRecipe_Parent();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.interpreter.rete.recipes.OuterJoinNodeRecipe#getDefaultValue <em>Default Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Default Value</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.OuterJoinNodeRecipe#getDefaultValue()
	 * @see #getOuterJoinNodeRecipe()
	 * @generated
	 */
	EAttribute getOuterJoinNodeRecipe_DefaultValue();

	/**
	 * Returns the meta object for the '{@link tools.refinery.interpreter.rete.recipes.OuterJoinNodeRecipe#getArity() <em>Get Arity</em>}' operation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the '<em>Get Arity</em>' operation.
	 * @see tools.refinery.interpreter.rete.recipes.OuterJoinNodeRecipe#getArity()
	 * @generated
	 */
	EOperation getOuterJoinNodeRecipe__GetArity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.interpreter.rete.recipes.OuterJoinIndexerRecipe <em>Outer Join Indexer Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Outer Join Indexer Recipe</em>'.
	 * @see tools.refinery.interpreter.rete.recipes.OuterJoinIndexerRecipe
	 * @generated
	 */
	EClass getOuterJoinIndexerRecipe();

	/**
	 * Returns the meta object for data type '{@link java.lang.Integer <em>Index</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
     * <!-- begin-model-doc -->
     * Indexes tell which variable of tuples are relevant for a given operation.
     * TODO: is this necessary at all?
     * <!-- end-model-doc -->
	 * @return the meta object for data type '<em>Index</em>'.
	 * @see java.lang.Integer
	 * @model instanceClass="java.lang.Integer"
	 * @generated
	 */
	EDataType getIndex();

	/**
	 * Returns the meta object for data type '{@link tools.refinery.interpreter.matchers.psystem.aggregations.IMultisetAggregationOperator <em>Aggregation Operator</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for data type '<em>Aggregation Operator</em>'.
	 * @see tools.refinery.interpreter.matchers.psystem.aggregations.IMultisetAggregationOperator
	 * @model instanceClass="tools.refinery.interpreter.matchers.psystem.aggregations.IMultisetAggregationOperator&lt;?, ?, ?&gt;"
	 * @generated
	 */
	EDataType getAggregationOperator();

	/**
	 * Returns the meta object for data type '{@link tools.refinery.interpreter.matchers.psystem.basicenumerables.Connectivity <em>Connectivity</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for data type '<em>Connectivity</em>'.
	 * @see tools.refinery.interpreter.matchers.psystem.basicenumerables.Connectivity
	 * @model instanceClass="tools.refinery.interpreter.matchers.psystem.basicenumerables.Connectivity"
	 * @generated
	 */
	EDataType getConnectivity();

	/**
	 * Returns the factory that creates the instances of the model.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the factory that creates the instances of the model.
	 * @generated
	 */
	RecipesFactory getRecipesFactory();

	/**
	 * <!-- begin-user-doc -->
	 * Defines literals for the meta objects that represent
	 * <ul>
	 *   <li>each class,</li>
	 *   <li>each feature of each class,</li>
	 *   <li>each operation of each class,</li>
	 *   <li>each enum,</li>
	 *   <li>and each data type</li>
	 * </ul>
	 * <!-- end-user-doc -->
	 * @generated
	 */
	interface Literals
	{
		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.ReteRecipeImpl <em>Rete Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.ReteRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getReteRecipe()
		 * @generated
		 */
		EClass RETE_RECIPE = eINSTANCE.getReteRecipe();

		/**
		 * The meta object literal for the '<em><b>Recipe Nodes</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference RETE_RECIPE__RECIPE_NODES = eINSTANCE.getReteRecipe_RecipeNodes();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.ReteNodeRecipeImpl <em>Rete Node Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.ReteNodeRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getReteNodeRecipe()
		 * @generated
		 */
		EClass RETE_NODE_RECIPE = eINSTANCE.getReteNodeRecipe();

		/**
		 * The meta object literal for the '<em><b>Trace Info</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute RETE_NODE_RECIPE__TRACE_INFO = eINSTANCE.getReteNodeRecipe_TraceInfo();

		/**
		 * The meta object literal for the '<em><b>Equivalence Class IDs</b></em>' attribute list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @since 1.3
		 * @generated
		 */
		EAttribute RETE_NODE_RECIPE__EQUIVALENCE_CLASS_IDS = eINSTANCE.getReteNodeRecipe_EquivalenceClassIDs();

		/**
		 * The meta object literal for the '<em><b>Cached Hash Code</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute RETE_NODE_RECIPE__CACHED_HASH_CODE = eINSTANCE.getReteNodeRecipe_CachedHashCode();

		/**
		 * The meta object literal for the '<em><b>Constructed</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute RETE_NODE_RECIPE__CONSTRUCTED = eINSTANCE.getReteNodeRecipe_Constructed();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation RETE_NODE_RECIPE___GET_ARITY = eINSTANCE.getReteNodeRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.SingleParentNodeRecipeImpl <em>Single Parent Node Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.SingleParentNodeRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getSingleParentNodeRecipe()
		 * @generated
		 */
		EClass SINGLE_PARENT_NODE_RECIPE = eINSTANCE.getSingleParentNodeRecipe();

		/**
		 * The meta object literal for the '<em><b>Parent</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference SINGLE_PARENT_NODE_RECIPE__PARENT = eINSTANCE.getSingleParentNodeRecipe_Parent();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.AlphaRecipeImpl <em>Alpha Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.AlphaRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getAlphaRecipe()
		 * @generated
		 */
		EClass ALPHA_RECIPE = eINSTANCE.getAlphaRecipe();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.MultiParentNodeRecipeImpl <em>Multi Parent Node Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.MultiParentNodeRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getMultiParentNodeRecipe()
		 * @generated
		 */
		EClass MULTI_PARENT_NODE_RECIPE = eINSTANCE.getMultiParentNodeRecipe();

		/**
		 * The meta object literal for the '<em><b>Parents</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference MULTI_PARENT_NODE_RECIPE__PARENTS = eINSTANCE.getMultiParentNodeRecipe_Parents();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation MULTI_PARENT_NODE_RECIPE___GET_ARITY = eINSTANCE.getMultiParentNodeRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.MonotonicityInfoImpl <em>Monotonicity Info</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.MonotonicityInfoImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getMonotonicityInfo()
		 * @generated
		 */
		EClass MONOTONICITY_INFO = eINSTANCE.getMonotonicityInfo();

		/**
		 * The meta object literal for the '<em><b>Core Mask</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference MONOTONICITY_INFO__CORE_MASK = eINSTANCE.getMonotonicityInfo_CoreMask();

		/**
		 * The meta object literal for the '<em><b>Poset Mask</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference MONOTONICITY_INFO__POSET_MASK = eINSTANCE.getMonotonicityInfo_PosetMask();

		/**
		 * The meta object literal for the '<em><b>Poset Comparator</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute MONOTONICITY_INFO__POSET_COMPARATOR = eINSTANCE.getMonotonicityInfo_PosetComparator();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.UniquenessEnforcerRecipeImpl <em>Uniqueness Enforcer Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.UniquenessEnforcerRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getUniquenessEnforcerRecipe()
		 * @generated
		 */
		EClass UNIQUENESS_ENFORCER_RECIPE = eINSTANCE.getUniquenessEnforcerRecipe();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.ProductionRecipeImpl <em>Production Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.ProductionRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getProductionRecipe()
		 * @generated
		 */
		EClass PRODUCTION_RECIPE = eINSTANCE.getProductionRecipe();

		/**
		 * The meta object literal for the '<em><b>Mapped Indices</b></em>' map feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PRODUCTION_RECIPE__MAPPED_INDICES = eINSTANCE.getProductionRecipe_MappedIndices();

		/**
		 * The meta object literal for the '<em><b>Pattern</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute PRODUCTION_RECIPE__PATTERN = eINSTANCE.getProductionRecipe_Pattern();

		/**
		 * The meta object literal for the '<em><b>Pattern FQN</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute PRODUCTION_RECIPE__PATTERN_FQN = eINSTANCE.getProductionRecipe_PatternFQN();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation PRODUCTION_RECIPE___GET_ARITY = eINSTANCE.getProductionRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.IndexerRecipeImpl <em>Indexer Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.IndexerRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getIndexerRecipe()
		 * @generated
		 */
		EClass INDEXER_RECIPE = eINSTANCE.getIndexerRecipe();

		/**
		 * The meta object literal for the '<em><b>Mask</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference INDEXER_RECIPE__MASK = eINSTANCE.getIndexerRecipe_Mask();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation INDEXER_RECIPE___GET_ARITY = eINSTANCE.getIndexerRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.ProjectionIndexerRecipeImpl <em>Projection Indexer Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.ProjectionIndexerRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getProjectionIndexerRecipe()
		 * @generated
		 */
		EClass PROJECTION_INDEXER_RECIPE = eINSTANCE.getProjectionIndexerRecipe();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.AggregatorIndexerRecipeImpl <em>Aggregator Indexer Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.AggregatorIndexerRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getAggregatorIndexerRecipe()
		 * @generated
		 */
		EClass AGGREGATOR_INDEXER_RECIPE = eINSTANCE.getAggregatorIndexerRecipe();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.BetaRecipeImpl <em>Beta Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.BetaRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getBetaRecipe()
		 * @generated
		 */
		EClass BETA_RECIPE = eINSTANCE.getBetaRecipe();

		/**
		 * The meta object literal for the '<em><b>Left Parent</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference BETA_RECIPE__LEFT_PARENT = eINSTANCE.getBetaRecipe_LeftParent();

		/**
		 * The meta object literal for the '<em><b>Right Parent</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference BETA_RECIPE__RIGHT_PARENT = eINSTANCE.getBetaRecipe_RightParent();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.MaskImpl <em>Mask</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.MaskImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getMask()
		 * @generated
		 */
		EClass MASK = eINSTANCE.getMask();

		/**
		 * The meta object literal for the '<em><b>Source Indices</b></em>' attribute list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute MASK__SOURCE_INDICES = eINSTANCE.getMask_SourceIndices();

		/**
		 * The meta object literal for the '<em><b>Source Arity</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute MASK__SOURCE_ARITY = eINSTANCE.getMask_SourceArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.StringIndexMapEntryImpl <em>String Index Map Entry</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.StringIndexMapEntryImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getStringIndexMapEntry()
		 * @generated
		 */
		EClass STRING_INDEX_MAP_ENTRY = eINSTANCE.getStringIndexMapEntry();

		/**
		 * The meta object literal for the '<em><b>Key</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute STRING_INDEX_MAP_ENTRY__KEY = eINSTANCE.getStringIndexMapEntry_Key();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute STRING_INDEX_MAP_ENTRY__VALUE = eINSTANCE.getStringIndexMapEntry_Value();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.InputRecipeImpl <em>Input Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.InputRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getInputRecipe()
		 * @generated
		 */
		EClass INPUT_RECIPE = eINSTANCE.getInputRecipe();

		/**
		 * The meta object literal for the '<em><b>Input Key</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute INPUT_RECIPE__INPUT_KEY = eINSTANCE.getInputRecipe_InputKey();

		/**
		 * The meta object literal for the '<em><b>Key ID</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute INPUT_RECIPE__KEY_ID = eINSTANCE.getInputRecipe_KeyID();

		/**
		 * The meta object literal for the '<em><b>Key Arity</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute INPUT_RECIPE__KEY_ARITY = eINSTANCE.getInputRecipe_KeyArity();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation INPUT_RECIPE___GET_ARITY = eINSTANCE.getInputRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.ConstantRecipeImpl <em>Constant Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.ConstantRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getConstantRecipe()
		 * @generated
		 */
		EClass CONSTANT_RECIPE = eINSTANCE.getConstantRecipe();

		/**
		 * The meta object literal for the '<em><b>Constant Values</b></em>' attribute list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute CONSTANT_RECIPE__CONSTANT_VALUES = eINSTANCE.getConstantRecipe_ConstantValues();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation CONSTANT_RECIPE___GET_ARITY = eINSTANCE.getConstantRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.TransitiveClosureRecipeImpl <em>Transitive Closure Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.TransitiveClosureRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getTransitiveClosureRecipe()
		 * @generated
		 */
		EClass TRANSITIVE_CLOSURE_RECIPE = eINSTANCE.getTransitiveClosureRecipe();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation TRANSITIVE_CLOSURE_RECIPE___GET_ARITY = eINSTANCE.getTransitiveClosureRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.FilterRecipeImpl <em>Filter Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.FilterRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getFilterRecipe()
		 * @generated
		 */
		EClass FILTER_RECIPE = eINSTANCE.getFilterRecipe();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation FILTER_RECIPE___GET_ARITY = eINSTANCE.getFilterRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.InequalityFilterRecipeImpl <em>Inequality Filter Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.InequalityFilterRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getInequalityFilterRecipe()
		 * @generated
		 */
		EClass INEQUALITY_FILTER_RECIPE = eINSTANCE.getInequalityFilterRecipe();

		/**
		 * The meta object literal for the '<em><b>Subject</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute INEQUALITY_FILTER_RECIPE__SUBJECT = eINSTANCE.getInequalityFilterRecipe_Subject();

		/**
		 * The meta object literal for the '<em><b>Inequals</b></em>' attribute list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute INEQUALITY_FILTER_RECIPE__INEQUALS = eINSTANCE.getInequalityFilterRecipe_Inequals();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.EqualityFilterRecipeImpl <em>Equality Filter Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.EqualityFilterRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getEqualityFilterRecipe()
		 * @generated
		 */
		EClass EQUALITY_FILTER_RECIPE = eINSTANCE.getEqualityFilterRecipe();

		/**
		 * The meta object literal for the '<em><b>Indices</b></em>' attribute list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute EQUALITY_FILTER_RECIPE__INDICES = eINSTANCE.getEqualityFilterRecipe_Indices();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.TransparentRecipeImpl <em>Transparent Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.TransparentRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getTransparentRecipe()
		 * @generated
		 */
		EClass TRANSPARENT_RECIPE = eINSTANCE.getTransparentRecipe();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.TrimmerRecipeImpl <em>Trimmer Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.TrimmerRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getTrimmerRecipe()
		 * @generated
		 */
		EClass TRIMMER_RECIPE = eINSTANCE.getTrimmerRecipe();

		/**
		 * The meta object literal for the '<em><b>Mask</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference TRIMMER_RECIPE__MASK = eINSTANCE.getTrimmerRecipe_Mask();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation TRIMMER_RECIPE___GET_ARITY = eINSTANCE.getTrimmerRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.ExpressionDefinitionImpl <em>Expression Definition</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.ExpressionDefinitionImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getExpressionDefinition()
		 * @generated
		 */
		EClass EXPRESSION_DEFINITION = eINSTANCE.getExpressionDefinition();

		/**
		 * The meta object literal for the '<em><b>Evaluator</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute EXPRESSION_DEFINITION__EVALUATOR = eINSTANCE.getExpressionDefinition_Evaluator();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.ExpressionEnforcerRecipeImpl <em>Expression Enforcer Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.ExpressionEnforcerRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getExpressionEnforcerRecipe()
		 * @generated
		 */
		EClass EXPRESSION_ENFORCER_RECIPE = eINSTANCE.getExpressionEnforcerRecipe();

		/**
		 * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference EXPRESSION_ENFORCER_RECIPE__EXPRESSION = eINSTANCE.getExpressionEnforcerRecipe_Expression();

		/**
		 * The meta object literal for the '<em><b>Mapped Indices</b></em>' map feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference EXPRESSION_ENFORCER_RECIPE__MAPPED_INDICES = eINSTANCE.getExpressionEnforcerRecipe_MappedIndices();

		/**
		 * The meta object literal for the '<em><b>Cache Output</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute EXPRESSION_ENFORCER_RECIPE__CACHE_OUTPUT = eINSTANCE.getExpressionEnforcerRecipe_CacheOutput();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.CheckRecipeImpl <em>Check Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.CheckRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getCheckRecipe()
		 * @generated
		 */
		EClass CHECK_RECIPE = eINSTANCE.getCheckRecipe();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation CHECK_RECIPE___GET_ARITY = eINSTANCE.getCheckRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.EvalRecipeImpl <em>Eval Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.EvalRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getEvalRecipe()
		 * @generated
		 */
		EClass EVAL_RECIPE = eINSTANCE.getEvalRecipe();

		/**
		 * The meta object literal for the '<em><b>Unwinding</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @since 2.4
		 * @generated
		 */
		EAttribute EVAL_RECIPE__UNWINDING = eINSTANCE.getEvalRecipe_Unwinding();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation EVAL_RECIPE___GET_ARITY = eINSTANCE.getEvalRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.IndexerBasedAggregatorRecipeImpl <em>Indexer Based Aggregator Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.IndexerBasedAggregatorRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getIndexerBasedAggregatorRecipe()
		 * @generated
		 */
		EClass INDEXER_BASED_AGGREGATOR_RECIPE = eINSTANCE.getIndexerBasedAggregatorRecipe();

		/**
		 * The meta object literal for the '<em><b>Parent</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference INDEXER_BASED_AGGREGATOR_RECIPE__PARENT = eINSTANCE.getIndexerBasedAggregatorRecipe_Parent();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation INDEXER_BASED_AGGREGATOR_RECIPE___GET_ARITY = eINSTANCE.getIndexerBasedAggregatorRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.CountAggregatorRecipeImpl <em>Count Aggregator Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.CountAggregatorRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getCountAggregatorRecipe()
		 * @generated
		 */
		EClass COUNT_AGGREGATOR_RECIPE = eINSTANCE.getCountAggregatorRecipe();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.JoinRecipeImpl <em>Join Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.JoinRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getJoinRecipe()
		 * @generated
		 */
		EClass JOIN_RECIPE = eINSTANCE.getJoinRecipe();

		/**
		 * The meta object literal for the '<em><b>Right Parent Complementary Mask</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference JOIN_RECIPE__RIGHT_PARENT_COMPLEMENTARY_MASK = eINSTANCE.getJoinRecipe_RightParentComplementaryMask();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation JOIN_RECIPE___GET_ARITY = eINSTANCE.getJoinRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.ExistenceJoinRecipeImpl <em>Existence Join Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.ExistenceJoinRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getExistenceJoinRecipe()
		 * @generated
		 */
		EClass EXISTENCE_JOIN_RECIPE = eINSTANCE.getExistenceJoinRecipe();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation EXISTENCE_JOIN_RECIPE___GET_ARITY = eINSTANCE.getExistenceJoinRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.SemiJoinRecipeImpl <em>Semi Join Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.SemiJoinRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getSemiJoinRecipe()
		 * @generated
		 */
		EClass SEMI_JOIN_RECIPE = eINSTANCE.getSemiJoinRecipe();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.AntiJoinRecipeImpl <em>Anti Join Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.AntiJoinRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getAntiJoinRecipe()
		 * @generated
		 */
		EClass ANTI_JOIN_RECIPE = eINSTANCE.getAntiJoinRecipe();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.InputFilterRecipeImpl <em>Input Filter Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.InputFilterRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getInputFilterRecipe()
		 * @generated
		 */
		EClass INPUT_FILTER_RECIPE = eINSTANCE.getInputFilterRecipe();

		/**
		 * The meta object literal for the '<em><b>Input Key</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute INPUT_FILTER_RECIPE__INPUT_KEY = eINSTANCE.getInputFilterRecipe_InputKey();

		/**
		 * The meta object literal for the '<em><b>Key ID</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute INPUT_FILTER_RECIPE__KEY_ID = eINSTANCE.getInputFilterRecipe_KeyID();

		/**
		 * The meta object literal for the '<em><b>Mask</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference INPUT_FILTER_RECIPE__MASK = eINSTANCE.getInputFilterRecipe_Mask();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.SingleColumnAggregatorRecipeImpl <em>Single Column Aggregator Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.SingleColumnAggregatorRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getSingleColumnAggregatorRecipe()
		 * @generated
		 */
		EClass SINGLE_COLUMN_AGGREGATOR_RECIPE = eINSTANCE.getSingleColumnAggregatorRecipe();

		/**
		 * The meta object literal for the '<em><b>Multiset Aggregation Operator</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute SINGLE_COLUMN_AGGREGATOR_RECIPE__MULTISET_AGGREGATION_OPERATOR = eINSTANCE.getSingleColumnAggregatorRecipe_MultisetAggregationOperator();

		/**
		 * The meta object literal for the '<em><b>Aggregable Index</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute SINGLE_COLUMN_AGGREGATOR_RECIPE__AGGREGABLE_INDEX = eINSTANCE.getSingleColumnAggregatorRecipe_AggregableIndex();

		/**
		 * The meta object literal for the '<em><b>Group By Mask</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference SINGLE_COLUMN_AGGREGATOR_RECIPE__GROUP_BY_MASK = eINSTANCE.getSingleColumnAggregatorRecipe_GroupByMask();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation SINGLE_COLUMN_AGGREGATOR_RECIPE___GET_ARITY = eINSTANCE.getSingleColumnAggregatorRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.DiscriminatorDispatcherRecipeImpl <em>Discriminator Dispatcher Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.DiscriminatorDispatcherRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getDiscriminatorDispatcherRecipe()
		 * @generated
		 */
		EClass DISCRIMINATOR_DISPATCHER_RECIPE = eINSTANCE.getDiscriminatorDispatcherRecipe();

		/**
		 * The meta object literal for the '<em><b>Discrimination Column Index</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute DISCRIMINATOR_DISPATCHER_RECIPE__DISCRIMINATION_COLUMN_INDEX = eINSTANCE.getDiscriminatorDispatcherRecipe_DiscriminationColumnIndex();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation DISCRIMINATOR_DISPATCHER_RECIPE___GET_ARITY = eINSTANCE.getDiscriminatorDispatcherRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.DiscriminatorBucketRecipeImpl <em>Discriminator Bucket Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.DiscriminatorBucketRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getDiscriminatorBucketRecipe()
		 * @generated
		 */
		EClass DISCRIMINATOR_BUCKET_RECIPE = eINSTANCE.getDiscriminatorBucketRecipe();

		/**
		 * The meta object literal for the '<em><b>Bucket Key</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute DISCRIMINATOR_BUCKET_RECIPE__BUCKET_KEY = eINSTANCE.getDiscriminatorBucketRecipe_BucketKey();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation DISCRIMINATOR_BUCKET_RECIPE___GET_ARITY = eINSTANCE.getDiscriminatorBucketRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.RederivableNodeRecipeImpl <em>Rederivable Node Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.RederivableNodeRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getRederivableNodeRecipe()
		 * @generated
		 */
		EClass REDERIVABLE_NODE_RECIPE = eINSTANCE.getRederivableNodeRecipe();

		/**
		 * The meta object literal for the '<em><b>Delete Rederive Evaluation</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute REDERIVABLE_NODE_RECIPE__DELETE_REDERIVE_EVALUATION = eINSTANCE.getRederivableNodeRecipe_DeleteRederiveEvaluation();

		/**
		 * The meta object literal for the '<em><b>Optional Monotonicity Info</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference REDERIVABLE_NODE_RECIPE__OPTIONAL_MONOTONICITY_INFO = eINSTANCE.getRederivableNodeRecipe_OptionalMonotonicityInfo();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.RelationEvaluationRecipeImpl <em>Relation Evaluation Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.RelationEvaluationRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getRelationEvaluationRecipe()
		 * @since 2.8
		 * @generated
		 */
		EClass RELATION_EVALUATION_RECIPE = eINSTANCE.getRelationEvaluationRecipe();

		/**
		 * The meta object literal for the '<em><b>Evaluator</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @since 2.8
		 * @generated
		 */
		EReference RELATION_EVALUATION_RECIPE__EVALUATOR = eINSTANCE.getRelationEvaluationRecipe_Evaluator();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.RepresentativeElectionRecipeImpl <em>Representative Election Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.RepresentativeElectionRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getRepresentativeElectionRecipe()
		 * @generated
		 */
		EClass REPRESENTATIVE_ELECTION_RECIPE = eINSTANCE.getRepresentativeElectionRecipe();

		/**
		 * The meta object literal for the '<em><b>Connectivity</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute REPRESENTATIVE_ELECTION_RECIPE__CONNECTIVITY = eINSTANCE.getRepresentativeElectionRecipe_Connectivity();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation REPRESENTATIVE_ELECTION_RECIPE___GET_ARITY = eINSTANCE.getRepresentativeElectionRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.OuterJoinNodeRecipeImpl <em>Outer Join Node Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.OuterJoinNodeRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getOuterJoinNodeRecipe()
		 * @generated
		 */
		EClass OUTER_JOIN_NODE_RECIPE = eINSTANCE.getOuterJoinNodeRecipe();

		/**
		 * The meta object literal for the '<em><b>Parent</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference OUTER_JOIN_NODE_RECIPE__PARENT = eINSTANCE.getOuterJoinNodeRecipe_Parent();

		/**
		 * The meta object literal for the '<em><b>Default Value</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute OUTER_JOIN_NODE_RECIPE__DEFAULT_VALUE = eINSTANCE.getOuterJoinNodeRecipe_DefaultValue();

		/**
		 * The meta object literal for the '<em><b>Get Arity</b></em>' operation.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EOperation OUTER_JOIN_NODE_RECIPE___GET_ARITY = eINSTANCE.getOuterJoinNodeRecipe__GetArity();

		/**
		 * The meta object literal for the '{@link tools.refinery.interpreter.rete.recipes.impl.OuterJoinIndexerRecipeImpl <em>Outer Join Indexer Recipe</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.rete.recipes.impl.OuterJoinIndexerRecipeImpl
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getOuterJoinIndexerRecipe()
		 * @generated
		 */
		EClass OUTER_JOIN_INDEXER_RECIPE = eINSTANCE.getOuterJoinIndexerRecipe();

		/**
		 * The meta object literal for the '<em>Index</em>' data type.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see java.lang.Integer
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getIndex()
		 * @generated
		 */
		EDataType INDEX = eINSTANCE.getIndex();

		/**
		 * The meta object literal for the '<em>Aggregation Operator</em>' data type.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.matchers.psystem.aggregations.IMultisetAggregationOperator
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getAggregationOperator()
		 * @generated
		 */
		EDataType AGGREGATION_OPERATOR = eINSTANCE.getAggregationOperator();

		/**
		 * The meta object literal for the '<em>Connectivity</em>' data type.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.interpreter.matchers.psystem.basicenumerables.Connectivity
		 * @see tools.refinery.interpreter.rete.recipes.impl.RecipesPackageImpl#getConnectivity()
		 * @generated
		 */
		EDataType CONNECTIVITY = eINSTANCE.getConnectivity();

	}

} //RecipesPackage
