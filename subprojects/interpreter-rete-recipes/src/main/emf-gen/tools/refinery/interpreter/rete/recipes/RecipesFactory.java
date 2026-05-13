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

import org.eclipse.emf.ecore.EFactory;

/**
 * <!-- begin-user-doc -->
 * The <b>Factory</b> for the model.
 * It provides a create method for each non-abstract class of the model.
 * <!-- end-user-doc -->
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage
 * @generated
 */
public interface RecipesFactory extends EFactory
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * The singleton instance of the factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	RecipesFactory eINSTANCE = tools.refinery.interpreter.rete.recipes.impl.RecipesFactoryImpl.init();

	/**
	 * Returns a new object of class '<em>Rete Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Rete Recipe</em>'.
	 * @generated
	 */
	ReteRecipe createReteRecipe();

	/**
	 * Returns a new object of class '<em>Monotonicity Info</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Monotonicity Info</em>'.
	 * @generated
	 */
	MonotonicityInfo createMonotonicityInfo();

	/**
	 * Returns a new object of class '<em>Uniqueness Enforcer Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Uniqueness Enforcer Recipe</em>'.
	 * @generated
	 */
	UniquenessEnforcerRecipe createUniquenessEnforcerRecipe();

	/**
	 * Returns a new object of class '<em>Production Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Production Recipe</em>'.
	 * @generated
	 */
	ProductionRecipe createProductionRecipe();

	/**
	 * Returns a new object of class '<em>Projection Indexer Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Projection Indexer Recipe</em>'.
	 * @generated
	 */
	ProjectionIndexerRecipe createProjectionIndexerRecipe();

	/**
	 * Returns a new object of class '<em>Aggregator Indexer Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Aggregator Indexer Recipe</em>'.
	 * @generated
	 */
	AggregatorIndexerRecipe createAggregatorIndexerRecipe();

	/**
	 * Returns a new object of class '<em>Mask</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Mask</em>'.
	 * @generated
	 */
	Mask createMask();

	/**
	 * Returns a new object of class '<em>Input Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Input Recipe</em>'.
	 * @generated
	 */
	InputRecipe createInputRecipe();

	/**
	 * Returns a new object of class '<em>Constant Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Constant Recipe</em>'.
	 * @generated
	 */
	ConstantRecipe createConstantRecipe();

	/**
	 * Returns a new object of class '<em>Transitive Closure Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Transitive Closure Recipe</em>'.
	 * @generated
	 */
	TransitiveClosureRecipe createTransitiveClosureRecipe();

	/**
	 * Returns a new object of class '<em>Inequality Filter Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Inequality Filter Recipe</em>'.
	 * @generated
	 */
	InequalityFilterRecipe createInequalityFilterRecipe();

	/**
	 * Returns a new object of class '<em>Equality Filter Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Equality Filter Recipe</em>'.
	 * @generated
	 */
	EqualityFilterRecipe createEqualityFilterRecipe();

	/**
	 * Returns a new object of class '<em>Transparent Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Transparent Recipe</em>'.
	 * @generated
	 */
	TransparentRecipe createTransparentRecipe();

	/**
	 * Returns a new object of class '<em>Trimmer Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Trimmer Recipe</em>'.
	 * @generated
	 */
	TrimmerRecipe createTrimmerRecipe();

	/**
	 * Returns a new object of class '<em>Expression Definition</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Expression Definition</em>'.
	 * @generated
	 */
	ExpressionDefinition createExpressionDefinition();

	/**
	 * Returns a new object of class '<em>Check Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Check Recipe</em>'.
	 * @generated
	 */
	CheckRecipe createCheckRecipe();

	/**
	 * Returns a new object of class '<em>Eval Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Eval Recipe</em>'.
	 * @generated
	 */
	EvalRecipe createEvalRecipe();

	/**
	 * Returns a new object of class '<em>Count Aggregator Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Count Aggregator Recipe</em>'.
	 * @generated
	 */
	CountAggregatorRecipe createCountAggregatorRecipe();

	/**
	 * Returns a new object of class '<em>Join Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Join Recipe</em>'.
	 * @generated
	 */
	JoinRecipe createJoinRecipe();

	/**
	 * Returns a new object of class '<em>Semi Join Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Semi Join Recipe</em>'.
	 * @generated
	 */
	SemiJoinRecipe createSemiJoinRecipe();

	/**
	 * Returns a new object of class '<em>Anti Join Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Anti Join Recipe</em>'.
	 * @generated
	 */
	AntiJoinRecipe createAntiJoinRecipe();

	/**
	 * Returns a new object of class '<em>Input Filter Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Input Filter Recipe</em>'.
	 * @generated
	 */
	InputFilterRecipe createInputFilterRecipe();

	/**
	 * Returns a new object of class '<em>Single Column Aggregator Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Single Column Aggregator Recipe</em>'.
	 * @generated
	 */
	SingleColumnAggregatorRecipe createSingleColumnAggregatorRecipe();

	/**
	 * Returns a new object of class '<em>Discriminator Dispatcher Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Discriminator Dispatcher Recipe</em>'.
	 * @generated
	 */
	DiscriminatorDispatcherRecipe createDiscriminatorDispatcherRecipe();

	/**
	 * Returns a new object of class '<em>Discriminator Bucket Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Discriminator Bucket Recipe</em>'.
	 * @generated
	 */
	DiscriminatorBucketRecipe createDiscriminatorBucketRecipe();

	/**
	 * Returns a new object of class '<em>Relation Evaluation Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Relation Evaluation Recipe</em>'.
	 * @since 2.8
	 * @generated
	 */
	RelationEvaluationRecipe createRelationEvaluationRecipe();

	/**
	 * Returns a new object of class '<em>Representative Election Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Representative Election Recipe</em>'.
	 * @generated
	 */
	RepresentativeElectionRecipe createRepresentativeElectionRecipe();

	/**
	 * Returns a new object of class '<em>Outer Join Node Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Outer Join Node Recipe</em>'.
	 * @generated
	 */
	OuterJoinNodeRecipe createOuterJoinNodeRecipe();

	/**
	 * Returns a new object of class '<em>Outer Join Indexer Recipe</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Outer Join Indexer Recipe</em>'.
	 * @generated
	 */
	OuterJoinIndexerRecipe createOuterJoinIndexerRecipe();

	/**
	 * Returns the package supported by this factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the package supported by this factory.
	 * @generated
	 */
	RecipesPackage getRecipesPackage();

} //RecipesFactory
