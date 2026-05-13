/**
 * Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro
 * Copyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License v. 2.0 which is available at
 * http://www.eclipse.org/legal/epl-v20.html.
 * 
 * SPDX-License-Identifier: EPL-2.0
 */
package tools.refinery.interpreter.rete.recipes.impl;

import java.util.Map;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EDataType;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;

import org.eclipse.emf.ecore.impl.EFactoryImpl;

import org.eclipse.emf.ecore.plugin.EcorePlugin;

import tools.refinery.interpreter.matchers.psystem.aggregations.IMultisetAggregationOperator;

import tools.refinery.interpreter.matchers.psystem.basicenumerables.Connectivity;

import tools.refinery.interpreter.rete.recipes.*;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model <b>Factory</b>.
 * <!-- end-user-doc -->
 * @generated
 */
public class RecipesFactoryImpl extends EFactoryImpl implements RecipesFactory
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static final String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * Creates the default factory implementation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static RecipesFactory init()
	{
		try
		{
			RecipesFactory theRecipesFactory = (RecipesFactory)EPackage.Registry.INSTANCE.getEFactory(RecipesPackage.eNS_URI);
			if (theRecipesFactory != null)
			{
				return theRecipesFactory;
			}
		}
		catch (Exception exception)
		{
			EcorePlugin.INSTANCE.log(exception);
		}
		return new RecipesFactoryImpl();
	}

	/**
	 * Creates an instance of the factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public RecipesFactoryImpl()
	{
		super();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EObject create(EClass eClass)
	{
		switch (eClass.getClassifierID())
		{
			case RecipesPackage.RETE_RECIPE: return createReteRecipe();
			case RecipesPackage.MONOTONICITY_INFO: return createMonotonicityInfo();
			case RecipesPackage.UNIQUENESS_ENFORCER_RECIPE: return createUniquenessEnforcerRecipe();
			case RecipesPackage.PRODUCTION_RECIPE: return createProductionRecipe();
			case RecipesPackage.PROJECTION_INDEXER_RECIPE: return createProjectionIndexerRecipe();
			case RecipesPackage.AGGREGATOR_INDEXER_RECIPE: return createAggregatorIndexerRecipe();
			case RecipesPackage.MASK: return createMask();
			case RecipesPackage.STRING_INDEX_MAP_ENTRY: return (EObject)createStringIndexMapEntry();
			case RecipesPackage.INPUT_RECIPE: return createInputRecipe();
			case RecipesPackage.CONSTANT_RECIPE: return createConstantRecipe();
			case RecipesPackage.TRANSITIVE_CLOSURE_RECIPE: return createTransitiveClosureRecipe();
			case RecipesPackage.INEQUALITY_FILTER_RECIPE: return createInequalityFilterRecipe();
			case RecipesPackage.EQUALITY_FILTER_RECIPE: return createEqualityFilterRecipe();
			case RecipesPackage.TRANSPARENT_RECIPE: return createTransparentRecipe();
			case RecipesPackage.TRIMMER_RECIPE: return createTrimmerRecipe();
			case RecipesPackage.EXPRESSION_DEFINITION: return createExpressionDefinition();
			case RecipesPackage.CHECK_RECIPE: return createCheckRecipe();
			case RecipesPackage.EVAL_RECIPE: return createEvalRecipe();
			case RecipesPackage.COUNT_AGGREGATOR_RECIPE: return createCountAggregatorRecipe();
			case RecipesPackage.JOIN_RECIPE: return createJoinRecipe();
			case RecipesPackage.SEMI_JOIN_RECIPE: return createSemiJoinRecipe();
			case RecipesPackage.ANTI_JOIN_RECIPE: return createAntiJoinRecipe();
			case RecipesPackage.INPUT_FILTER_RECIPE: return createInputFilterRecipe();
			case RecipesPackage.SINGLE_COLUMN_AGGREGATOR_RECIPE: return createSingleColumnAggregatorRecipe();
			case RecipesPackage.DISCRIMINATOR_DISPATCHER_RECIPE: return createDiscriminatorDispatcherRecipe();
			case RecipesPackage.DISCRIMINATOR_BUCKET_RECIPE: return createDiscriminatorBucketRecipe();
			case RecipesPackage.RELATION_EVALUATION_RECIPE: return createRelationEvaluationRecipe();
			case RecipesPackage.REPRESENTATIVE_ELECTION_RECIPE: return createRepresentativeElectionRecipe();
			case RecipesPackage.OUTER_JOIN_NODE_RECIPE: return createOuterJoinNodeRecipe();
			case RecipesPackage.OUTER_JOIN_INDEXER_RECIPE: return createOuterJoinIndexerRecipe();
			default:
				throw new IllegalArgumentException("The class '" + eClass.getName() + "' is not a valid classifier"); //$NON-NLS-1$ //$NON-NLS-2$
		}
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object createFromString(EDataType eDataType, String initialValue)
	{
		switch (eDataType.getClassifierID())
		{
			case RecipesPackage.INDEX:
				return createIndexFromString(eDataType, initialValue);
			case RecipesPackage.AGGREGATION_OPERATOR:
				return createAggregationOperatorFromString(eDataType, initialValue);
			case RecipesPackage.CONNECTIVITY:
				return createConnectivityFromString(eDataType, initialValue);
			default:
				throw new IllegalArgumentException("The datatype '" + eDataType.getName() + "' is not a valid classifier"); //$NON-NLS-1$ //$NON-NLS-2$
		}
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public String convertToString(EDataType eDataType, Object instanceValue)
	{
		switch (eDataType.getClassifierID())
		{
			case RecipesPackage.INDEX:
				return convertIndexToString(eDataType, instanceValue);
			case RecipesPackage.AGGREGATION_OPERATOR:
				return convertAggregationOperatorToString(eDataType, instanceValue);
			case RecipesPackage.CONNECTIVITY:
				return convertConnectivityToString(eDataType, instanceValue);
			default:
				throw new IllegalArgumentException("The datatype '" + eDataType.getName() + "' is not a valid classifier"); //$NON-NLS-1$ //$NON-NLS-2$
		}
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public ReteRecipe createReteRecipe()
	{
		ReteRecipeImpl reteRecipe = new ReteRecipeImpl();
		return reteRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public MonotonicityInfo createMonotonicityInfo()
	{
		MonotonicityInfoImpl monotonicityInfo = new MonotonicityInfoImpl();
		return monotonicityInfo;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public UniquenessEnforcerRecipe createUniquenessEnforcerRecipe()
	{
		UniquenessEnforcerRecipeImpl uniquenessEnforcerRecipe = new UniquenessEnforcerRecipeImpl();
		return uniquenessEnforcerRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public ProductionRecipe createProductionRecipe()
	{
		ProductionRecipeImpl productionRecipe = new ProductionRecipeImpl();
		return productionRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public ProjectionIndexerRecipe createProjectionIndexerRecipe()
	{
		ProjectionIndexerRecipeImpl projectionIndexerRecipe = new ProjectionIndexerRecipeImpl();
		return projectionIndexerRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public AggregatorIndexerRecipe createAggregatorIndexerRecipe()
	{
		AggregatorIndexerRecipeImpl aggregatorIndexerRecipe = new AggregatorIndexerRecipeImpl();
		return aggregatorIndexerRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Mask createMask()
	{
		MaskImpl mask = new MaskImpl();
		return mask;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Map.Entry<String, Integer> createStringIndexMapEntry()
	{
		StringIndexMapEntryImpl stringIndexMapEntry = new StringIndexMapEntryImpl();
		return stringIndexMapEntry;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public InputRecipe createInputRecipe()
	{
		InputRecipeImpl inputRecipe = new InputRecipeImpl();
		return inputRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public ConstantRecipe createConstantRecipe()
	{
		ConstantRecipeImpl constantRecipe = new ConstantRecipeImpl();
		return constantRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public TransitiveClosureRecipe createTransitiveClosureRecipe()
	{
		TransitiveClosureRecipeImpl transitiveClosureRecipe = new TransitiveClosureRecipeImpl();
		return transitiveClosureRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public InequalityFilterRecipe createInequalityFilterRecipe()
	{
		InequalityFilterRecipeImpl inequalityFilterRecipe = new InequalityFilterRecipeImpl();
		return inequalityFilterRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EqualityFilterRecipe createEqualityFilterRecipe()
	{
		EqualityFilterRecipeImpl equalityFilterRecipe = new EqualityFilterRecipeImpl();
		return equalityFilterRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public TransparentRecipe createTransparentRecipe()
	{
		TransparentRecipeImpl transparentRecipe = new TransparentRecipeImpl();
		return transparentRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public TrimmerRecipe createTrimmerRecipe()
	{
		TrimmerRecipeImpl trimmerRecipe = new TrimmerRecipeImpl();
		return trimmerRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public ExpressionDefinition createExpressionDefinition()
	{
		ExpressionDefinitionImpl expressionDefinition = new ExpressionDefinitionImpl();
		return expressionDefinition;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public CheckRecipe createCheckRecipe()
	{
		CheckRecipeImpl checkRecipe = new CheckRecipeImpl();
		return checkRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EvalRecipe createEvalRecipe()
	{
		EvalRecipeImpl evalRecipe = new EvalRecipeImpl();
		return evalRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public CountAggregatorRecipe createCountAggregatorRecipe()
	{
		CountAggregatorRecipeImpl countAggregatorRecipe = new CountAggregatorRecipeImpl();
		return countAggregatorRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public JoinRecipe createJoinRecipe()
	{
		JoinRecipeImpl joinRecipe = new JoinRecipeImpl();
		return joinRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public SemiJoinRecipe createSemiJoinRecipe()
	{
		SemiJoinRecipeImpl semiJoinRecipe = new SemiJoinRecipeImpl();
		return semiJoinRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public AntiJoinRecipe createAntiJoinRecipe()
	{
		AntiJoinRecipeImpl antiJoinRecipe = new AntiJoinRecipeImpl();
		return antiJoinRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public InputFilterRecipe createInputFilterRecipe()
	{
		InputFilterRecipeImpl inputFilterRecipe = new InputFilterRecipeImpl();
		return inputFilterRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public SingleColumnAggregatorRecipe createSingleColumnAggregatorRecipe()
	{
		SingleColumnAggregatorRecipeImpl singleColumnAggregatorRecipe = new SingleColumnAggregatorRecipeImpl();
		return singleColumnAggregatorRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public DiscriminatorDispatcherRecipe createDiscriminatorDispatcherRecipe()
	{
		DiscriminatorDispatcherRecipeImpl discriminatorDispatcherRecipe = new DiscriminatorDispatcherRecipeImpl();
		return discriminatorDispatcherRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public DiscriminatorBucketRecipe createDiscriminatorBucketRecipe()
	{
		DiscriminatorBucketRecipeImpl discriminatorBucketRecipe = new DiscriminatorBucketRecipeImpl();
		return discriminatorBucketRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 2.8
	 * @generated
	 */
	@Override
	public RelationEvaluationRecipe createRelationEvaluationRecipe()
	{
		RelationEvaluationRecipeImpl relationEvaluationRecipe = new RelationEvaluationRecipeImpl();
		return relationEvaluationRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public RepresentativeElectionRecipe createRepresentativeElectionRecipe()
	{
		RepresentativeElectionRecipeImpl representativeElectionRecipe = new RepresentativeElectionRecipeImpl();
		return representativeElectionRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public OuterJoinNodeRecipe createOuterJoinNodeRecipe()
	{
		OuterJoinNodeRecipeImpl outerJoinNodeRecipe = new OuterJoinNodeRecipeImpl();
		return outerJoinNodeRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public OuterJoinIndexerRecipe createOuterJoinIndexerRecipe()
	{
		OuterJoinIndexerRecipeImpl outerJoinIndexerRecipe = new OuterJoinIndexerRecipeImpl();
		return outerJoinIndexerRecipe;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Integer createIndexFromString(EDataType eDataType, String initialValue)
	{
		return (Integer)super.createFromString(eDataType, initialValue);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertIndexToString(EDataType eDataType, Object instanceValue)
	{
		return super.convertToString(eDataType, instanceValue);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public IMultisetAggregationOperator<?, ?, ?> createAggregationOperatorFromString(EDataType eDataType, String initialValue)
	{
		return (IMultisetAggregationOperator<?, ?, ?>)super.createFromString(initialValue);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertAggregationOperatorToString(EDataType eDataType, Object instanceValue)
	{
		return super.convertToString(instanceValue);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Connectivity createConnectivityFromString(EDataType eDataType, String initialValue)
	{
		return (Connectivity)super.createFromString(eDataType, initialValue);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertConnectivityToString(EDataType eDataType, Object instanceValue)
	{
		return super.convertToString(eDataType, instanceValue);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public RecipesPackage getRecipesPackage()
	{
		return (RecipesPackage)getEPackage();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @deprecated
	 * @generated
	 */
	@Deprecated
	public static RecipesPackage getPackage()
	{
		return RecipesPackage.eINSTANCE;
	}

} //RecipesFactoryImpl
