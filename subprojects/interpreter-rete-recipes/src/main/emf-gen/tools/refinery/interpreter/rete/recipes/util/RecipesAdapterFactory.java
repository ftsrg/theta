/**
 * Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro
 * Copyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License v. 2.0 which is available at
 * http://www.eclipse.org/legal/epl-v20.html.
 * 
 * SPDX-License-Identifier: EPL-2.0
 */
package tools.refinery.interpreter.rete.recipes.util;

import java.util.Map;

import org.eclipse.emf.common.notify.Adapter;
import org.eclipse.emf.common.notify.Notifier;

import org.eclipse.emf.common.notify.impl.AdapterFactoryImpl;

import org.eclipse.emf.ecore.EObject;

import tools.refinery.interpreter.rete.recipes.*;

/**
 * <!-- begin-user-doc -->
 * The <b>Adapter Factory</b> for the model.
 * It provides an adapter <code>createXXX</code> method for each class of the model.
 * <!-- end-user-doc -->
 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage
 * @generated
 */
public class RecipesAdapterFactory extends AdapterFactoryImpl
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static final String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * The cached model package.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected static RecipesPackage modelPackage;

	/**
	 * Creates an instance of the adapter factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public RecipesAdapterFactory()
	{
		if (modelPackage == null)
		{
			modelPackage = RecipesPackage.eINSTANCE;
		}
	}

	/**
	 * Returns whether this factory is applicable for the type of the object.
	 * <!-- begin-user-doc -->
	 * This implementation returns <code>true</code> if the object is either the model's package or is an instance object of the model.
	 * <!-- end-user-doc -->
	 * @return whether this factory is applicable for the type of the object.
	 * @generated
	 */
	@Override
	public boolean isFactoryForType(Object object)
	{
		if (object == modelPackage)
		{
			return true;
		}
		if (object instanceof EObject)
		{
			return ((EObject)object).eClass().getEPackage() == modelPackage;
		}
		return false;
	}

	/**
	 * The switch that delegates to the <code>createXXX</code> methods.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected RecipesSwitch<Adapter> modelSwitch =
		new RecipesSwitch<Adapter>()
		{
			@Override
			public Adapter caseReteRecipe(ReteRecipe object)
			{
				return createReteRecipeAdapter();
			}
			@Override
			public Adapter caseReteNodeRecipe(ReteNodeRecipe object)
			{
				return createReteNodeRecipeAdapter();
			}
			@Override
			public Adapter caseSingleParentNodeRecipe(SingleParentNodeRecipe object)
			{
				return createSingleParentNodeRecipeAdapter();
			}
			@Override
			public Adapter caseAlphaRecipe(AlphaRecipe object)
			{
				return createAlphaRecipeAdapter();
			}
			@Override
			public Adapter caseMultiParentNodeRecipe(MultiParentNodeRecipe object)
			{
				return createMultiParentNodeRecipeAdapter();
			}
			@Override
			public Adapter caseMonotonicityInfo(MonotonicityInfo object)
			{
				return createMonotonicityInfoAdapter();
			}
			@Override
			public Adapter caseUniquenessEnforcerRecipe(UniquenessEnforcerRecipe object)
			{
				return createUniquenessEnforcerRecipeAdapter();
			}
			@Override
			public Adapter caseProductionRecipe(ProductionRecipe object)
			{
				return createProductionRecipeAdapter();
			}
			@Override
			public Adapter caseIndexerRecipe(IndexerRecipe object)
			{
				return createIndexerRecipeAdapter();
			}
			@Override
			public Adapter caseProjectionIndexerRecipe(ProjectionIndexerRecipe object)
			{
				return createProjectionIndexerRecipeAdapter();
			}
			@Override
			public Adapter caseAggregatorIndexerRecipe(AggregatorIndexerRecipe object)
			{
				return createAggregatorIndexerRecipeAdapter();
			}
			@Override
			public Adapter caseBetaRecipe(BetaRecipe object)
			{
				return createBetaRecipeAdapter();
			}
			@Override
			public Adapter caseMask(Mask object)
			{
				return createMaskAdapter();
			}
			@Override
			public Adapter caseStringIndexMapEntry(Map.Entry<String, Integer> object)
			{
				return createStringIndexMapEntryAdapter();
			}
			@Override
			public Adapter caseInputRecipe(InputRecipe object)
			{
				return createInputRecipeAdapter();
			}
			@Override
			public Adapter caseConstantRecipe(ConstantRecipe object)
			{
				return createConstantRecipeAdapter();
			}
			@Override
			public Adapter caseTransitiveClosureRecipe(TransitiveClosureRecipe object)
			{
				return createTransitiveClosureRecipeAdapter();
			}
			@Override
			public Adapter caseFilterRecipe(FilterRecipe object)
			{
				return createFilterRecipeAdapter();
			}
			@Override
			public Adapter caseInequalityFilterRecipe(InequalityFilterRecipe object)
			{
				return createInequalityFilterRecipeAdapter();
			}
			@Override
			public Adapter caseEqualityFilterRecipe(EqualityFilterRecipe object)
			{
				return createEqualityFilterRecipeAdapter();
			}
			@Override
			public Adapter caseTransparentRecipe(TransparentRecipe object)
			{
				return createTransparentRecipeAdapter();
			}
			@Override
			public Adapter caseTrimmerRecipe(TrimmerRecipe object)
			{
				return createTrimmerRecipeAdapter();
			}
			@Override
			public Adapter caseExpressionDefinition(ExpressionDefinition object)
			{
				return createExpressionDefinitionAdapter();
			}
			@Override
			public Adapter caseExpressionEnforcerRecipe(ExpressionEnforcerRecipe object)
			{
				return createExpressionEnforcerRecipeAdapter();
			}
			@Override
			public Adapter caseCheckRecipe(CheckRecipe object)
			{
				return createCheckRecipeAdapter();
			}
			@Override
			public Adapter caseEvalRecipe(EvalRecipe object)
			{
				return createEvalRecipeAdapter();
			}
			@Override
			public Adapter caseIndexerBasedAggregatorRecipe(IndexerBasedAggregatorRecipe object)
			{
				return createIndexerBasedAggregatorRecipeAdapter();
			}
			@Override
			public Adapter caseCountAggregatorRecipe(CountAggregatorRecipe object)
			{
				return createCountAggregatorRecipeAdapter();
			}
			@Override
			public Adapter caseJoinRecipe(JoinRecipe object)
			{
				return createJoinRecipeAdapter();
			}
			@Override
			public Adapter caseExistenceJoinRecipe(ExistenceJoinRecipe object)
			{
				return createExistenceJoinRecipeAdapter();
			}
			@Override
			public Adapter caseSemiJoinRecipe(SemiJoinRecipe object)
			{
				return createSemiJoinRecipeAdapter();
			}
			@Override
			public Adapter caseAntiJoinRecipe(AntiJoinRecipe object)
			{
				return createAntiJoinRecipeAdapter();
			}
			@Override
			public Adapter caseInputFilterRecipe(InputFilterRecipe object)
			{
				return createInputFilterRecipeAdapter();
			}
			@Override
			public Adapter caseSingleColumnAggregatorRecipe(SingleColumnAggregatorRecipe object)
			{
				return createSingleColumnAggregatorRecipeAdapter();
			}
			@Override
			public Adapter caseDiscriminatorDispatcherRecipe(DiscriminatorDispatcherRecipe object)
			{
				return createDiscriminatorDispatcherRecipeAdapter();
			}
			@Override
			public Adapter caseDiscriminatorBucketRecipe(DiscriminatorBucketRecipe object)
			{
				return createDiscriminatorBucketRecipeAdapter();
			}
			@Override
			public Adapter caseRederivableNodeRecipe(RederivableNodeRecipe object)
			{
				return createRederivableNodeRecipeAdapter();
			}
			@Override
			public Adapter caseRelationEvaluationRecipe(RelationEvaluationRecipe object)
			{
				return createRelationEvaluationRecipeAdapter();
			}
			@Override
			public Adapter caseRepresentativeElectionRecipe(RepresentativeElectionRecipe object)
			{
				return createRepresentativeElectionRecipeAdapter();
			}
			@Override
			public Adapter caseOuterJoinNodeRecipe(OuterJoinNodeRecipe object)
			{
				return createOuterJoinNodeRecipeAdapter();
			}
			@Override
			public Adapter caseOuterJoinIndexerRecipe(OuterJoinIndexerRecipe object)
			{
				return createOuterJoinIndexerRecipeAdapter();
			}
			@Override
			public Adapter defaultCase(EObject object)
			{
				return createEObjectAdapter();
			}
		};

	/**
	 * Creates an adapter for the <code>target</code>.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param target the object to adapt.
	 * @return the adapter for the <code>target</code>.
	 * @generated
	 */
	@Override
	public Adapter createAdapter(Notifier target)
	{
		return modelSwitch.doSwitch((EObject)target);
	}


	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.ReteRecipe <em>Rete Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.ReteRecipe
	 * @generated
	 */
	public Adapter createReteRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.ReteNodeRecipe <em>Rete Node Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.ReteNodeRecipe
	 * @generated
	 */
	public Adapter createReteNodeRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.SingleParentNodeRecipe <em>Single Parent Node Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.SingleParentNodeRecipe
	 * @generated
	 */
	public Adapter createSingleParentNodeRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.AlphaRecipe <em>Alpha Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.AlphaRecipe
	 * @generated
	 */
	public Adapter createAlphaRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.MultiParentNodeRecipe <em>Multi Parent Node Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.MultiParentNodeRecipe
	 * @generated
	 */
	public Adapter createMultiParentNodeRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.MonotonicityInfo <em>Monotonicity Info</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.MonotonicityInfo
	 * @generated
	 */
	public Adapter createMonotonicityInfoAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.UniquenessEnforcerRecipe <em>Uniqueness Enforcer Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.UniquenessEnforcerRecipe
	 * @generated
	 */
	public Adapter createUniquenessEnforcerRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.ProductionRecipe <em>Production Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.ProductionRecipe
	 * @generated
	 */
	public Adapter createProductionRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.IndexerRecipe <em>Indexer Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.IndexerRecipe
	 * @generated
	 */
	public Adapter createIndexerRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.ProjectionIndexerRecipe <em>Projection Indexer Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.ProjectionIndexerRecipe
	 * @generated
	 */
	public Adapter createProjectionIndexerRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.AggregatorIndexerRecipe <em>Aggregator Indexer Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.AggregatorIndexerRecipe
	 * @generated
	 */
	public Adapter createAggregatorIndexerRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.BetaRecipe <em>Beta Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.BetaRecipe
	 * @generated
	 */
	public Adapter createBetaRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.Mask <em>Mask</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.Mask
	 * @generated
	 */
	public Adapter createMaskAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link java.util.Map.Entry <em>String Index Map Entry</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see java.util.Map.Entry
	 * @generated
	 */
	public Adapter createStringIndexMapEntryAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.InputRecipe <em>Input Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.InputRecipe
	 * @generated
	 */
	public Adapter createInputRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.ConstantRecipe <em>Constant Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.ConstantRecipe
	 * @generated
	 */
	public Adapter createConstantRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.TransitiveClosureRecipe <em>Transitive Closure Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.TransitiveClosureRecipe
	 * @generated
	 */
	public Adapter createTransitiveClosureRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.FilterRecipe <em>Filter Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.FilterRecipe
	 * @generated
	 */
	public Adapter createFilterRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.InequalityFilterRecipe <em>Inequality Filter Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.InequalityFilterRecipe
	 * @generated
	 */
	public Adapter createInequalityFilterRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.EqualityFilterRecipe <em>Equality Filter Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.EqualityFilterRecipe
	 * @generated
	 */
	public Adapter createEqualityFilterRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.TransparentRecipe <em>Transparent Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.TransparentRecipe
	 * @generated
	 */
	public Adapter createTransparentRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.TrimmerRecipe <em>Trimmer Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.TrimmerRecipe
	 * @generated
	 */
	public Adapter createTrimmerRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.ExpressionDefinition <em>Expression Definition</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.ExpressionDefinition
	 * @generated
	 */
	public Adapter createExpressionDefinitionAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.ExpressionEnforcerRecipe <em>Expression Enforcer Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.ExpressionEnforcerRecipe
	 * @generated
	 */
	public Adapter createExpressionEnforcerRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.CheckRecipe <em>Check Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.CheckRecipe
	 * @generated
	 */
	public Adapter createCheckRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.EvalRecipe <em>Eval Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.EvalRecipe
	 * @generated
	 */
	public Adapter createEvalRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.IndexerBasedAggregatorRecipe <em>Indexer Based Aggregator Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.IndexerBasedAggregatorRecipe
	 * @generated
	 */
	public Adapter createIndexerBasedAggregatorRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.CountAggregatorRecipe <em>Count Aggregator Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.CountAggregatorRecipe
	 * @generated
	 */
	public Adapter createCountAggregatorRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.JoinRecipe <em>Join Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.JoinRecipe
	 * @generated
	 */
	public Adapter createJoinRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.ExistenceJoinRecipe <em>Existence Join Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.ExistenceJoinRecipe
	 * @generated
	 */
	public Adapter createExistenceJoinRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.SemiJoinRecipe <em>Semi Join Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.SemiJoinRecipe
	 * @generated
	 */
	public Adapter createSemiJoinRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.AntiJoinRecipe <em>Anti Join Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.AntiJoinRecipe
	 * @generated
	 */
	public Adapter createAntiJoinRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.InputFilterRecipe <em>Input Filter Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.InputFilterRecipe
	 * @generated
	 */
	public Adapter createInputFilterRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe <em>Single Column Aggregator Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe
	 * @generated
	 */
	public Adapter createSingleColumnAggregatorRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.DiscriminatorDispatcherRecipe <em>Discriminator Dispatcher Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.DiscriminatorDispatcherRecipe
	 * @generated
	 */
	public Adapter createDiscriminatorDispatcherRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.DiscriminatorBucketRecipe <em>Discriminator Bucket Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.DiscriminatorBucketRecipe
	 * @generated
	 */
	public Adapter createDiscriminatorBucketRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.RederivableNodeRecipe <em>Rederivable Node Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.RederivableNodeRecipe
	 * @generated
	 */
	public Adapter createRederivableNodeRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.RelationEvaluationRecipe <em>Relation Evaluation Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.RelationEvaluationRecipe
	 * @since 2.8
	 * @generated
	 */
	public Adapter createRelationEvaluationRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.RepresentativeElectionRecipe <em>Representative Election Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.RepresentativeElectionRecipe
	 * @generated
	 */
	public Adapter createRepresentativeElectionRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.OuterJoinNodeRecipe <em>Outer Join Node Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.OuterJoinNodeRecipe
	 * @generated
	 */
	public Adapter createOuterJoinNodeRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.interpreter.rete.recipes.OuterJoinIndexerRecipe <em>Outer Join Indexer Recipe</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.interpreter.rete.recipes.OuterJoinIndexerRecipe
	 * @generated
	 */
	public Adapter createOuterJoinIndexerRecipeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for the default case.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @generated
	 */
	public Adapter createEObjectAdapter()
	{
		return null;
	}

} //RecipesAdapterFactory
