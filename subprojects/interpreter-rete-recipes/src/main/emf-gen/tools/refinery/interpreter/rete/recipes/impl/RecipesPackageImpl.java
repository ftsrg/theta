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

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EDataType;
import org.eclipse.emf.ecore.EOperation;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EReference;

import org.eclipse.emf.ecore.impl.EPackageImpl;

import tools.refinery.interpreter.matchers.psystem.aggregations.IMultisetAggregationOperator;

import tools.refinery.interpreter.matchers.psystem.basicenumerables.Connectivity;

import tools.refinery.interpreter.rete.recipes.AggregatorIndexerRecipe;
import tools.refinery.interpreter.rete.recipes.AlphaRecipe;
import tools.refinery.interpreter.rete.recipes.AntiJoinRecipe;
import tools.refinery.interpreter.rete.recipes.BetaRecipe;
import tools.refinery.interpreter.rete.recipes.CheckRecipe;
import tools.refinery.interpreter.rete.recipes.ConstantRecipe;
import tools.refinery.interpreter.rete.recipes.CountAggregatorRecipe;
import tools.refinery.interpreter.rete.recipes.DiscriminatorBucketRecipe;
import tools.refinery.interpreter.rete.recipes.DiscriminatorDispatcherRecipe;
import tools.refinery.interpreter.rete.recipes.EqualityFilterRecipe;
import tools.refinery.interpreter.rete.recipes.EvalRecipe;
import tools.refinery.interpreter.rete.recipes.ExistenceJoinRecipe;
import tools.refinery.interpreter.rete.recipes.ExpressionDefinition;
import tools.refinery.interpreter.rete.recipes.ExpressionEnforcerRecipe;
import tools.refinery.interpreter.rete.recipes.FilterRecipe;
import tools.refinery.interpreter.rete.recipes.IndexerBasedAggregatorRecipe;
import tools.refinery.interpreter.rete.recipes.IndexerRecipe;
import tools.refinery.interpreter.rete.recipes.InequalityFilterRecipe;
import tools.refinery.interpreter.rete.recipes.InputFilterRecipe;
import tools.refinery.interpreter.rete.recipes.InputRecipe;
import tools.refinery.interpreter.rete.recipes.JoinRecipe;
import tools.refinery.interpreter.rete.recipes.Mask;
import tools.refinery.interpreter.rete.recipes.MonotonicityInfo;
import tools.refinery.interpreter.rete.recipes.MultiParentNodeRecipe;
import tools.refinery.interpreter.rete.recipes.OuterJoinIndexerRecipe;
import tools.refinery.interpreter.rete.recipes.OuterJoinNodeRecipe;
import tools.refinery.interpreter.rete.recipes.ProductionRecipe;
import tools.refinery.interpreter.rete.recipes.ProjectionIndexerRecipe;
import tools.refinery.interpreter.rete.recipes.RecipesFactory;
import tools.refinery.interpreter.rete.recipes.RecipesPackage;
import tools.refinery.interpreter.rete.recipes.RederivableNodeRecipe;
import tools.refinery.interpreter.rete.recipes.RelationEvaluationRecipe;
import tools.refinery.interpreter.rete.recipes.RepresentativeElectionRecipe;
import tools.refinery.interpreter.rete.recipes.ReteNodeRecipe;
import tools.refinery.interpreter.rete.recipes.ReteRecipe;
import tools.refinery.interpreter.rete.recipes.SemiJoinRecipe;
import tools.refinery.interpreter.rete.recipes.SingleColumnAggregatorRecipe;
import tools.refinery.interpreter.rete.recipes.SingleParentNodeRecipe;
import tools.refinery.interpreter.rete.recipes.TransitiveClosureRecipe;
import tools.refinery.interpreter.rete.recipes.TransparentRecipe;
import tools.refinery.interpreter.rete.recipes.TrimmerRecipe;
import tools.refinery.interpreter.rete.recipes.UniquenessEnforcerRecipe;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model <b>Package</b>.
 * <!-- end-user-doc -->
 * @generated
 */
public class RecipesPackageImpl extends EPackageImpl implements RecipesPackage
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static final String copyright = "Copyright (c) 2004-2014 Gabor Bergmann and Daniel Varro\nCopyright (c) 2023-2024 The Refinery Authors <https://refinery.tools>\nThis program and the accompanying materials are made available under the\nterms of the Eclipse Public License v. 2.0 which is available at\nhttp://www.eclipse.org/legal/epl-v20.html.\n\nSPDX-License-Identifier: EPL-2.0"; //$NON-NLS-1$

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass reteRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass reteNodeRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass singleParentNodeRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass alphaRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass multiParentNodeRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass monotonicityInfoEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass uniquenessEnforcerRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass productionRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass indexerRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass projectionIndexerRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass aggregatorIndexerRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass betaRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass maskEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass stringIndexMapEntryEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass inputRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass constantRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass transitiveClosureRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass filterRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass inequalityFilterRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass equalityFilterRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass transparentRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass trimmerRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass expressionDefinitionEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass expressionEnforcerRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass checkRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass evalRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass indexerBasedAggregatorRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass countAggregatorRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass joinRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass existenceJoinRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass semiJoinRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass antiJoinRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass inputFilterRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass singleColumnAggregatorRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass discriminatorDispatcherRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass discriminatorBucketRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass rederivableNodeRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 2.8
	 * @generated
	 */
	private EClass relationEvaluationRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass representativeElectionRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass outerJoinNodeRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass outerJoinIndexerRecipeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EDataType indexEDataType = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EDataType aggregationOperatorEDataType = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EDataType connectivityEDataType = null;

	/**
	 * Creates an instance of the model <b>Package</b>, registered with
	 * {@link org.eclipse.emf.ecore.EPackage.Registry EPackage.Registry} by the package
	 * package URI value.
	 * <p>Note: the correct way to create the package is via the static
	 * factory method {@link #init init()}, which also performs
	 * initialization of the package, or returns the registered package,
	 * if one already exists.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.eclipse.emf.ecore.EPackage.Registry
	 * @see tools.refinery.interpreter.rete.recipes.RecipesPackage#eNS_URI
	 * @see #init()
	 * @generated
	 */
	private RecipesPackageImpl()
	{
		super(eNS_URI, RecipesFactory.eINSTANCE);
	}
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private static boolean isInited = false;

	/**
	 * Creates, registers, and initializes the <b>Package</b> for this model, and for any others upon which it depends.
	 *
	 * <p>This method is used to initialize {@link RecipesPackage#eINSTANCE} when that field is accessed.
	 * Clients should not invoke it directly. Instead, they should simply access that field to obtain the package.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #eNS_URI
	 * @see #createPackageContents()
	 * @see #initializePackageContents()
	 * @generated
	 */
	public static RecipesPackage init()
	{
		if (isInited) return (RecipesPackage)EPackage.Registry.INSTANCE.getEPackage(RecipesPackage.eNS_URI);

		// Obtain or create and register package
		Object registeredRecipesPackage = EPackage.Registry.INSTANCE.get(eNS_URI);
		RecipesPackageImpl theRecipesPackage = registeredRecipesPackage instanceof RecipesPackageImpl ? (RecipesPackageImpl)registeredRecipesPackage : new RecipesPackageImpl();

		isInited = true;

		// Create package meta-data objects
		theRecipesPackage.createPackageContents();

		// Initialize created meta-data
		theRecipesPackage.initializePackageContents();

		// Mark meta-data to indicate it can't be changed
		theRecipesPackage.freeze();

		// Update the registry and return the package
		EPackage.Registry.INSTANCE.put(RecipesPackage.eNS_URI, theRecipesPackage);
		return theRecipesPackage;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getReteRecipe()
	{
		return reteRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getReteRecipe_RecipeNodes()
	{
		return (EReference)reteRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getReteNodeRecipe()
	{
		return reteNodeRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getReteNodeRecipe_TraceInfo()
	{
		return (EAttribute)reteNodeRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 1.3
	 * @generated
	 */
	@Override
	public EAttribute getReteNodeRecipe_EquivalenceClassIDs()
	{
		return (EAttribute)reteNodeRecipeEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getReteNodeRecipe_CachedHashCode()
	{
		return (EAttribute)reteNodeRecipeEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getReteNodeRecipe_Constructed()
	{
		return (EAttribute)reteNodeRecipeEClass.getEStructuralFeatures().get(3);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getReteNodeRecipe__GetArity()
	{
		return reteNodeRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getSingleParentNodeRecipe()
	{
		return singleParentNodeRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getSingleParentNodeRecipe_Parent()
	{
		return (EReference)singleParentNodeRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getAlphaRecipe()
	{
		return alphaRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getMultiParentNodeRecipe()
	{
		return multiParentNodeRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getMultiParentNodeRecipe_Parents()
	{
		return (EReference)multiParentNodeRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getMultiParentNodeRecipe__GetArity()
	{
		return multiParentNodeRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getMonotonicityInfo()
	{
		return monotonicityInfoEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getMonotonicityInfo_CoreMask()
	{
		return (EReference)monotonicityInfoEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getMonotonicityInfo_PosetMask()
	{
		return (EReference)monotonicityInfoEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getMonotonicityInfo_PosetComparator()
	{
		return (EAttribute)monotonicityInfoEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getUniquenessEnforcerRecipe()
	{
		return uniquenessEnforcerRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getProductionRecipe()
	{
		return productionRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getProductionRecipe_MappedIndices()
	{
		return (EReference)productionRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getProductionRecipe_Pattern()
	{
		return (EAttribute)productionRecipeEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getProductionRecipe_PatternFQN()
	{
		return (EAttribute)productionRecipeEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getProductionRecipe__GetArity()
	{
		return productionRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getIndexerRecipe()
	{
		return indexerRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getIndexerRecipe_Mask()
	{
		return (EReference)indexerRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getIndexerRecipe__GetArity()
	{
		return indexerRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getProjectionIndexerRecipe()
	{
		return projectionIndexerRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getAggregatorIndexerRecipe()
	{
		return aggregatorIndexerRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getBetaRecipe()
	{
		return betaRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getBetaRecipe_LeftParent()
	{
		return (EReference)betaRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getBetaRecipe_RightParent()
	{
		return (EReference)betaRecipeEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getMask()
	{
		return maskEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getMask_SourceIndices()
	{
		return (EAttribute)maskEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getMask_SourceArity()
	{
		return (EAttribute)maskEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getStringIndexMapEntry()
	{
		return stringIndexMapEntryEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getStringIndexMapEntry_Key()
	{
		return (EAttribute)stringIndexMapEntryEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getStringIndexMapEntry_Value()
	{
		return (EAttribute)stringIndexMapEntryEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getInputRecipe()
	{
		return inputRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getInputRecipe_InputKey()
	{
		return (EAttribute)inputRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getInputRecipe_KeyID()
	{
		return (EAttribute)inputRecipeEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getInputRecipe_KeyArity()
	{
		return (EAttribute)inputRecipeEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getInputRecipe__GetArity()
	{
		return inputRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getConstantRecipe()
	{
		return constantRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getConstantRecipe_ConstantValues()
	{
		return (EAttribute)constantRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getConstantRecipe__GetArity()
	{
		return constantRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getTransitiveClosureRecipe()
	{
		return transitiveClosureRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getTransitiveClosureRecipe__GetArity()
	{
		return transitiveClosureRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getFilterRecipe()
	{
		return filterRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getFilterRecipe__GetArity()
	{
		return filterRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getInequalityFilterRecipe()
	{
		return inequalityFilterRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getInequalityFilterRecipe_Subject()
	{
		return (EAttribute)inequalityFilterRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getInequalityFilterRecipe_Inequals()
	{
		return (EAttribute)inequalityFilterRecipeEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getEqualityFilterRecipe()
	{
		return equalityFilterRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getEqualityFilterRecipe_Indices()
	{
		return (EAttribute)equalityFilterRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getTransparentRecipe()
	{
		return transparentRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getTrimmerRecipe()
	{
		return trimmerRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getTrimmerRecipe_Mask()
	{
		return (EReference)trimmerRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getTrimmerRecipe__GetArity()
	{
		return trimmerRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getExpressionDefinition()
	{
		return expressionDefinitionEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getExpressionDefinition_Evaluator()
	{
		return (EAttribute)expressionDefinitionEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getExpressionEnforcerRecipe()
	{
		return expressionEnforcerRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getExpressionEnforcerRecipe_Expression()
	{
		return (EReference)expressionEnforcerRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getExpressionEnforcerRecipe_MappedIndices()
	{
		return (EReference)expressionEnforcerRecipeEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getExpressionEnforcerRecipe_CacheOutput()
	{
		return (EAttribute)expressionEnforcerRecipeEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getCheckRecipe()
	{
		return checkRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getCheckRecipe__GetArity()
	{
		return checkRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getEvalRecipe()
	{
		return evalRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 2.4
	 * @generated
	 */
	@Override
	public EAttribute getEvalRecipe_Unwinding()
	{
		return (EAttribute)evalRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getEvalRecipe__GetArity()
	{
		return evalRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getIndexerBasedAggregatorRecipe()
	{
		return indexerBasedAggregatorRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getIndexerBasedAggregatorRecipe_Parent()
	{
		return (EReference)indexerBasedAggregatorRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getIndexerBasedAggregatorRecipe__GetArity()
	{
		return indexerBasedAggregatorRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getCountAggregatorRecipe()
	{
		return countAggregatorRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getJoinRecipe()
	{
		return joinRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getJoinRecipe_RightParentComplementaryMask()
	{
		return (EReference)joinRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getJoinRecipe__GetArity()
	{
		return joinRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getExistenceJoinRecipe()
	{
		return existenceJoinRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getExistenceJoinRecipe__GetArity()
	{
		return existenceJoinRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getSemiJoinRecipe()
	{
		return semiJoinRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getAntiJoinRecipe()
	{
		return antiJoinRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getInputFilterRecipe()
	{
		return inputFilterRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getInputFilterRecipe_InputKey()
	{
		return (EAttribute)inputFilterRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getInputFilterRecipe_KeyID()
	{
		return (EAttribute)inputFilterRecipeEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getInputFilterRecipe_Mask()
	{
		return (EReference)inputFilterRecipeEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getSingleColumnAggregatorRecipe()
	{
		return singleColumnAggregatorRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getSingleColumnAggregatorRecipe_MultisetAggregationOperator()
	{
		return (EAttribute)singleColumnAggregatorRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getSingleColumnAggregatorRecipe_AggregableIndex()
	{
		return (EAttribute)singleColumnAggregatorRecipeEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getSingleColumnAggregatorRecipe_GroupByMask()
	{
		return (EReference)singleColumnAggregatorRecipeEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getSingleColumnAggregatorRecipe__GetArity()
	{
		return singleColumnAggregatorRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getDiscriminatorDispatcherRecipe()
	{
		return discriminatorDispatcherRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getDiscriminatorDispatcherRecipe_DiscriminationColumnIndex()
	{
		return (EAttribute)discriminatorDispatcherRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getDiscriminatorDispatcherRecipe__GetArity()
	{
		return discriminatorDispatcherRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getDiscriminatorBucketRecipe()
	{
		return discriminatorBucketRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getDiscriminatorBucketRecipe_BucketKey()
	{
		return (EAttribute)discriminatorBucketRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getDiscriminatorBucketRecipe__GetArity()
	{
		return discriminatorBucketRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getRederivableNodeRecipe()
	{
		return rederivableNodeRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getRederivableNodeRecipe_DeleteRederiveEvaluation()
	{
		return (EAttribute)rederivableNodeRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getRederivableNodeRecipe_OptionalMonotonicityInfo()
	{
		return (EReference)rederivableNodeRecipeEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 2.8
	 * @generated
	 */
	@Override
	public EClass getRelationEvaluationRecipe()
	{
		return relationEvaluationRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @since 2.8
	 * @generated
	 */
	@Override
	public EReference getRelationEvaluationRecipe_Evaluator()
	{
		return (EReference)relationEvaluationRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getRepresentativeElectionRecipe()
	{
		return representativeElectionRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getRepresentativeElectionRecipe_Connectivity()
	{
		return (EAttribute)representativeElectionRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getRepresentativeElectionRecipe__GetArity()
	{
		return representativeElectionRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getOuterJoinNodeRecipe()
	{
		return outerJoinNodeRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EReference getOuterJoinNodeRecipe_Parent()
	{
		return (EReference)outerJoinNodeRecipeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EAttribute getOuterJoinNodeRecipe_DefaultValue()
	{
		return (EAttribute)outerJoinNodeRecipeEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EOperation getOuterJoinNodeRecipe__GetArity()
	{
		return outerJoinNodeRecipeEClass.getEOperations().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EClass getOuterJoinIndexerRecipe()
	{
		return outerJoinIndexerRecipeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EDataType getIndex()
	{
		return indexEDataType;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EDataType getAggregationOperator()
	{
		return aggregationOperatorEDataType;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EDataType getConnectivity()
	{
		return connectivityEDataType;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public RecipesFactory getRecipesFactory()
	{
		return (RecipesFactory)getEFactoryInstance();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private boolean isCreated = false;

	/**
	 * Creates the meta-model objects for the package.  This method is
	 * guarded to have no affect on any invocation but its first.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void createPackageContents()
	{
		if (isCreated) return;
		isCreated = true;

		// Create classes and their features
		reteRecipeEClass = createEClass(RETE_RECIPE);
		createEReference(reteRecipeEClass, RETE_RECIPE__RECIPE_NODES);

		reteNodeRecipeEClass = createEClass(RETE_NODE_RECIPE);
		createEAttribute(reteNodeRecipeEClass, RETE_NODE_RECIPE__TRACE_INFO);
		createEAttribute(reteNodeRecipeEClass, RETE_NODE_RECIPE__EQUIVALENCE_CLASS_IDS);
		createEAttribute(reteNodeRecipeEClass, RETE_NODE_RECIPE__CACHED_HASH_CODE);
		createEAttribute(reteNodeRecipeEClass, RETE_NODE_RECIPE__CONSTRUCTED);
		createEOperation(reteNodeRecipeEClass, RETE_NODE_RECIPE___GET_ARITY);

		singleParentNodeRecipeEClass = createEClass(SINGLE_PARENT_NODE_RECIPE);
		createEReference(singleParentNodeRecipeEClass, SINGLE_PARENT_NODE_RECIPE__PARENT);

		alphaRecipeEClass = createEClass(ALPHA_RECIPE);

		multiParentNodeRecipeEClass = createEClass(MULTI_PARENT_NODE_RECIPE);
		createEReference(multiParentNodeRecipeEClass, MULTI_PARENT_NODE_RECIPE__PARENTS);
		createEOperation(multiParentNodeRecipeEClass, MULTI_PARENT_NODE_RECIPE___GET_ARITY);

		monotonicityInfoEClass = createEClass(MONOTONICITY_INFO);
		createEReference(monotonicityInfoEClass, MONOTONICITY_INFO__CORE_MASK);
		createEReference(monotonicityInfoEClass, MONOTONICITY_INFO__POSET_MASK);
		createEAttribute(monotonicityInfoEClass, MONOTONICITY_INFO__POSET_COMPARATOR);

		uniquenessEnforcerRecipeEClass = createEClass(UNIQUENESS_ENFORCER_RECIPE);

		productionRecipeEClass = createEClass(PRODUCTION_RECIPE);
		createEReference(productionRecipeEClass, PRODUCTION_RECIPE__MAPPED_INDICES);
		createEAttribute(productionRecipeEClass, PRODUCTION_RECIPE__PATTERN);
		createEAttribute(productionRecipeEClass, PRODUCTION_RECIPE__PATTERN_FQN);
		createEOperation(productionRecipeEClass, PRODUCTION_RECIPE___GET_ARITY);

		indexerRecipeEClass = createEClass(INDEXER_RECIPE);
		createEReference(indexerRecipeEClass, INDEXER_RECIPE__MASK);
		createEOperation(indexerRecipeEClass, INDEXER_RECIPE___GET_ARITY);

		projectionIndexerRecipeEClass = createEClass(PROJECTION_INDEXER_RECIPE);

		aggregatorIndexerRecipeEClass = createEClass(AGGREGATOR_INDEXER_RECIPE);

		betaRecipeEClass = createEClass(BETA_RECIPE);
		createEReference(betaRecipeEClass, BETA_RECIPE__LEFT_PARENT);
		createEReference(betaRecipeEClass, BETA_RECIPE__RIGHT_PARENT);

		maskEClass = createEClass(MASK);
		createEAttribute(maskEClass, MASK__SOURCE_INDICES);
		createEAttribute(maskEClass, MASK__SOURCE_ARITY);

		stringIndexMapEntryEClass = createEClass(STRING_INDEX_MAP_ENTRY);
		createEAttribute(stringIndexMapEntryEClass, STRING_INDEX_MAP_ENTRY__KEY);
		createEAttribute(stringIndexMapEntryEClass, STRING_INDEX_MAP_ENTRY__VALUE);

		inputRecipeEClass = createEClass(INPUT_RECIPE);
		createEAttribute(inputRecipeEClass, INPUT_RECIPE__INPUT_KEY);
		createEAttribute(inputRecipeEClass, INPUT_RECIPE__KEY_ID);
		createEAttribute(inputRecipeEClass, INPUT_RECIPE__KEY_ARITY);
		createEOperation(inputRecipeEClass, INPUT_RECIPE___GET_ARITY);

		constantRecipeEClass = createEClass(CONSTANT_RECIPE);
		createEAttribute(constantRecipeEClass, CONSTANT_RECIPE__CONSTANT_VALUES);
		createEOperation(constantRecipeEClass, CONSTANT_RECIPE___GET_ARITY);

		transitiveClosureRecipeEClass = createEClass(TRANSITIVE_CLOSURE_RECIPE);
		createEOperation(transitiveClosureRecipeEClass, TRANSITIVE_CLOSURE_RECIPE___GET_ARITY);

		filterRecipeEClass = createEClass(FILTER_RECIPE);
		createEOperation(filterRecipeEClass, FILTER_RECIPE___GET_ARITY);

		inequalityFilterRecipeEClass = createEClass(INEQUALITY_FILTER_RECIPE);
		createEAttribute(inequalityFilterRecipeEClass, INEQUALITY_FILTER_RECIPE__SUBJECT);
		createEAttribute(inequalityFilterRecipeEClass, INEQUALITY_FILTER_RECIPE__INEQUALS);

		equalityFilterRecipeEClass = createEClass(EQUALITY_FILTER_RECIPE);
		createEAttribute(equalityFilterRecipeEClass, EQUALITY_FILTER_RECIPE__INDICES);

		transparentRecipeEClass = createEClass(TRANSPARENT_RECIPE);

		trimmerRecipeEClass = createEClass(TRIMMER_RECIPE);
		createEReference(trimmerRecipeEClass, TRIMMER_RECIPE__MASK);
		createEOperation(trimmerRecipeEClass, TRIMMER_RECIPE___GET_ARITY);

		expressionDefinitionEClass = createEClass(EXPRESSION_DEFINITION);
		createEAttribute(expressionDefinitionEClass, EXPRESSION_DEFINITION__EVALUATOR);

		expressionEnforcerRecipeEClass = createEClass(EXPRESSION_ENFORCER_RECIPE);
		createEReference(expressionEnforcerRecipeEClass, EXPRESSION_ENFORCER_RECIPE__EXPRESSION);
		createEReference(expressionEnforcerRecipeEClass, EXPRESSION_ENFORCER_RECIPE__MAPPED_INDICES);
		createEAttribute(expressionEnforcerRecipeEClass, EXPRESSION_ENFORCER_RECIPE__CACHE_OUTPUT);

		checkRecipeEClass = createEClass(CHECK_RECIPE);
		createEOperation(checkRecipeEClass, CHECK_RECIPE___GET_ARITY);

		evalRecipeEClass = createEClass(EVAL_RECIPE);
		createEAttribute(evalRecipeEClass, EVAL_RECIPE__UNWINDING);
		createEOperation(evalRecipeEClass, EVAL_RECIPE___GET_ARITY);

		indexerBasedAggregatorRecipeEClass = createEClass(INDEXER_BASED_AGGREGATOR_RECIPE);
		createEReference(indexerBasedAggregatorRecipeEClass, INDEXER_BASED_AGGREGATOR_RECIPE__PARENT);
		createEOperation(indexerBasedAggregatorRecipeEClass, INDEXER_BASED_AGGREGATOR_RECIPE___GET_ARITY);

		countAggregatorRecipeEClass = createEClass(COUNT_AGGREGATOR_RECIPE);

		joinRecipeEClass = createEClass(JOIN_RECIPE);
		createEReference(joinRecipeEClass, JOIN_RECIPE__RIGHT_PARENT_COMPLEMENTARY_MASK);
		createEOperation(joinRecipeEClass, JOIN_RECIPE___GET_ARITY);

		existenceJoinRecipeEClass = createEClass(EXISTENCE_JOIN_RECIPE);
		createEOperation(existenceJoinRecipeEClass, EXISTENCE_JOIN_RECIPE___GET_ARITY);

		semiJoinRecipeEClass = createEClass(SEMI_JOIN_RECIPE);

		antiJoinRecipeEClass = createEClass(ANTI_JOIN_RECIPE);

		inputFilterRecipeEClass = createEClass(INPUT_FILTER_RECIPE);
		createEAttribute(inputFilterRecipeEClass, INPUT_FILTER_RECIPE__INPUT_KEY);
		createEAttribute(inputFilterRecipeEClass, INPUT_FILTER_RECIPE__KEY_ID);
		createEReference(inputFilterRecipeEClass, INPUT_FILTER_RECIPE__MASK);

		singleColumnAggregatorRecipeEClass = createEClass(SINGLE_COLUMN_AGGREGATOR_RECIPE);
		createEAttribute(singleColumnAggregatorRecipeEClass, SINGLE_COLUMN_AGGREGATOR_RECIPE__MULTISET_AGGREGATION_OPERATOR);
		createEAttribute(singleColumnAggregatorRecipeEClass, SINGLE_COLUMN_AGGREGATOR_RECIPE__AGGREGABLE_INDEX);
		createEReference(singleColumnAggregatorRecipeEClass, SINGLE_COLUMN_AGGREGATOR_RECIPE__GROUP_BY_MASK);
		createEOperation(singleColumnAggregatorRecipeEClass, SINGLE_COLUMN_AGGREGATOR_RECIPE___GET_ARITY);

		discriminatorDispatcherRecipeEClass = createEClass(DISCRIMINATOR_DISPATCHER_RECIPE);
		createEAttribute(discriminatorDispatcherRecipeEClass, DISCRIMINATOR_DISPATCHER_RECIPE__DISCRIMINATION_COLUMN_INDEX);
		createEOperation(discriminatorDispatcherRecipeEClass, DISCRIMINATOR_DISPATCHER_RECIPE___GET_ARITY);

		discriminatorBucketRecipeEClass = createEClass(DISCRIMINATOR_BUCKET_RECIPE);
		createEAttribute(discriminatorBucketRecipeEClass, DISCRIMINATOR_BUCKET_RECIPE__BUCKET_KEY);
		createEOperation(discriminatorBucketRecipeEClass, DISCRIMINATOR_BUCKET_RECIPE___GET_ARITY);

		rederivableNodeRecipeEClass = createEClass(REDERIVABLE_NODE_RECIPE);
		createEAttribute(rederivableNodeRecipeEClass, REDERIVABLE_NODE_RECIPE__DELETE_REDERIVE_EVALUATION);
		createEReference(rederivableNodeRecipeEClass, REDERIVABLE_NODE_RECIPE__OPTIONAL_MONOTONICITY_INFO);

		relationEvaluationRecipeEClass = createEClass(RELATION_EVALUATION_RECIPE);
		createEReference(relationEvaluationRecipeEClass, RELATION_EVALUATION_RECIPE__EVALUATOR);

		representativeElectionRecipeEClass = createEClass(REPRESENTATIVE_ELECTION_RECIPE);
		createEAttribute(representativeElectionRecipeEClass, REPRESENTATIVE_ELECTION_RECIPE__CONNECTIVITY);
		createEOperation(representativeElectionRecipeEClass, REPRESENTATIVE_ELECTION_RECIPE___GET_ARITY);

		outerJoinNodeRecipeEClass = createEClass(OUTER_JOIN_NODE_RECIPE);
		createEReference(outerJoinNodeRecipeEClass, OUTER_JOIN_NODE_RECIPE__PARENT);
		createEAttribute(outerJoinNodeRecipeEClass, OUTER_JOIN_NODE_RECIPE__DEFAULT_VALUE);
		createEOperation(outerJoinNodeRecipeEClass, OUTER_JOIN_NODE_RECIPE___GET_ARITY);

		outerJoinIndexerRecipeEClass = createEClass(OUTER_JOIN_INDEXER_RECIPE);

		// Create data types
		indexEDataType = createEDataType(INDEX);
		aggregationOperatorEDataType = createEDataType(AGGREGATION_OPERATOR);
		connectivityEDataType = createEDataType(CONNECTIVITY);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private boolean isInitialized = false;

	/**
	 * Complete the initialization of the package and its meta-model.  This
	 * method is guarded to have no affect on any invocation but its first.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void initializePackageContents()
	{
		if (isInitialized) return;
		isInitialized = true;

		// Initialize package
		setName(eNAME);
		setNsPrefix(eNS_PREFIX);
		setNsURI(eNS_URI);

		// Create type parameters

		// Set bounds for type parameters

		// Add supertypes to classes
		singleParentNodeRecipeEClass.getESuperTypes().add(this.getReteNodeRecipe());
		alphaRecipeEClass.getESuperTypes().add(this.getSingleParentNodeRecipe());
		multiParentNodeRecipeEClass.getESuperTypes().add(this.getReteNodeRecipe());
		uniquenessEnforcerRecipeEClass.getESuperTypes().add(this.getMultiParentNodeRecipe());
		uniquenessEnforcerRecipeEClass.getESuperTypes().add(this.getRederivableNodeRecipe());
		productionRecipeEClass.getESuperTypes().add(this.getMultiParentNodeRecipe());
		productionRecipeEClass.getESuperTypes().add(this.getRederivableNodeRecipe());
		indexerRecipeEClass.getESuperTypes().add(this.getSingleParentNodeRecipe());
		projectionIndexerRecipeEClass.getESuperTypes().add(this.getIndexerRecipe());
		aggregatorIndexerRecipeEClass.getESuperTypes().add(this.getIndexerRecipe());
		betaRecipeEClass.getESuperTypes().add(this.getReteNodeRecipe());
		inputRecipeEClass.getESuperTypes().add(this.getReteNodeRecipe());
		constantRecipeEClass.getESuperTypes().add(this.getReteNodeRecipe());
		transitiveClosureRecipeEClass.getESuperTypes().add(this.getAlphaRecipe());
		filterRecipeEClass.getESuperTypes().add(this.getAlphaRecipe());
		inequalityFilterRecipeEClass.getESuperTypes().add(this.getFilterRecipe());
		equalityFilterRecipeEClass.getESuperTypes().add(this.getFilterRecipe());
		transparentRecipeEClass.getESuperTypes().add(this.getFilterRecipe());
		trimmerRecipeEClass.getESuperTypes().add(this.getAlphaRecipe());
		expressionEnforcerRecipeEClass.getESuperTypes().add(this.getAlphaRecipe());
		checkRecipeEClass.getESuperTypes().add(this.getExpressionEnforcerRecipe());
		evalRecipeEClass.getESuperTypes().add(this.getExpressionEnforcerRecipe());
		indexerBasedAggregatorRecipeEClass.getESuperTypes().add(this.getReteNodeRecipe());
		countAggregatorRecipeEClass.getESuperTypes().add(this.getIndexerBasedAggregatorRecipe());
		joinRecipeEClass.getESuperTypes().add(this.getBetaRecipe());
		existenceJoinRecipeEClass.getESuperTypes().add(this.getBetaRecipe());
		semiJoinRecipeEClass.getESuperTypes().add(this.getExistenceJoinRecipe());
		antiJoinRecipeEClass.getESuperTypes().add(this.getExistenceJoinRecipe());
		inputFilterRecipeEClass.getESuperTypes().add(this.getFilterRecipe());
		singleColumnAggregatorRecipeEClass.getESuperTypes().add(this.getAlphaRecipe());
		singleColumnAggregatorRecipeEClass.getESuperTypes().add(this.getRederivableNodeRecipe());
		discriminatorDispatcherRecipeEClass.getESuperTypes().add(this.getSingleParentNodeRecipe());
		discriminatorBucketRecipeEClass.getESuperTypes().add(this.getSingleParentNodeRecipe());
		relationEvaluationRecipeEClass.getESuperTypes().add(this.getMultiParentNodeRecipe());
		representativeElectionRecipeEClass.getESuperTypes().add(this.getAlphaRecipe());
		outerJoinNodeRecipeEClass.getESuperTypes().add(this.getReteNodeRecipe());
		outerJoinIndexerRecipeEClass.getESuperTypes().add(this.getIndexerRecipe());

		// Initialize classes, features, and operations; add parameters
		initEClass(reteRecipeEClass, ReteRecipe.class, "ReteRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEReference(getReteRecipe_RecipeNodes(), this.getReteNodeRecipe(), null, "recipeNodes", null, 0, -1, ReteRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEClass(reteNodeRecipeEClass, ReteNodeRecipe.class, "ReteNodeRecipe", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEAttribute(getReteNodeRecipe_TraceInfo(), ecorePackage.getEString(), "traceInfo", null, 0, 1, ReteNodeRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, !IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEAttribute(getReteNodeRecipe_EquivalenceClassIDs(), ecorePackage.getELong(), "equivalenceClassIDs", null, 0, -1, ReteNodeRecipe.class, IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEAttribute(getReteNodeRecipe_CachedHashCode(), ecorePackage.getELongObject(), "cachedHashCode", null, 0, 1, ReteNodeRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEAttribute(getReteNodeRecipe_Constructed(), ecorePackage.getEBoolean(), "constructed", null, 0, 1, ReteNodeRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEOperation(getReteNodeRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(singleParentNodeRecipeEClass, SingleParentNodeRecipe.class, "SingleParentNodeRecipe", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEReference(getSingleParentNodeRecipe_Parent(), this.getReteNodeRecipe(), null, "parent", null, 0, 1, SingleParentNodeRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEClass(alphaRecipeEClass, AlphaRecipe.class, "AlphaRecipe", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$

		initEClass(multiParentNodeRecipeEClass, MultiParentNodeRecipe.class, "MultiParentNodeRecipe", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEReference(getMultiParentNodeRecipe_Parents(), this.getReteNodeRecipe(), null, "parents", null, 0, -1, MultiParentNodeRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEOperation(getMultiParentNodeRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(monotonicityInfoEClass, MonotonicityInfo.class, "MonotonicityInfo", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEReference(getMonotonicityInfo_CoreMask(), this.getMask(), null, "coreMask", null, 0, 1, MonotonicityInfo.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEReference(getMonotonicityInfo_PosetMask(), this.getMask(), null, "posetMask", null, 0, 1, MonotonicityInfo.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEAttribute(getMonotonicityInfo_PosetComparator(), ecorePackage.getEJavaObject(), "posetComparator", null, 0, 1, MonotonicityInfo.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEClass(uniquenessEnforcerRecipeEClass, UniquenessEnforcerRecipe.class, "UniquenessEnforcerRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$

		initEClass(productionRecipeEClass, ProductionRecipe.class, "ProductionRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEReference(getProductionRecipe_MappedIndices(), this.getStringIndexMapEntry(), null, "mappedIndices", null, 0, -1, ProductionRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEAttribute(getProductionRecipe_Pattern(), ecorePackage.getEJavaObject(), "pattern", null, 0, 1, ProductionRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, !IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEAttribute(getProductionRecipe_PatternFQN(), ecorePackage.getEString(), "patternFQN", null, 0, 1, ProductionRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEOperation(getProductionRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(indexerRecipeEClass, IndexerRecipe.class, "IndexerRecipe", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEReference(getIndexerRecipe_Mask(), this.getMask(), null, "mask", null, 0, 1, IndexerRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEOperation(getIndexerRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(projectionIndexerRecipeEClass, ProjectionIndexerRecipe.class, "ProjectionIndexerRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$

		initEClass(aggregatorIndexerRecipeEClass, AggregatorIndexerRecipe.class, "AggregatorIndexerRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$

		initEClass(betaRecipeEClass, BetaRecipe.class, "BetaRecipe", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEReference(getBetaRecipe_LeftParent(), this.getProjectionIndexerRecipe(), null, "leftParent", null, 0, 1, BetaRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEReference(getBetaRecipe_RightParent(), this.getIndexerRecipe(), null, "rightParent", null, 0, 1, BetaRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEClass(maskEClass, Mask.class, "Mask", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEAttribute(getMask_SourceIndices(), this.getIndex(), "sourceIndices", null, 0, -1, Mask.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, !IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEAttribute(getMask_SourceArity(), ecorePackage.getEInt(), "sourceArity", null, 0, 1, Mask.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, !IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEClass(stringIndexMapEntryEClass, Map.Entry.class, "StringIndexMapEntry", !IS_ABSTRACT, !IS_INTERFACE, !IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEAttribute(getStringIndexMapEntry_Key(), ecorePackage.getEString(), "key", null, 0, 1, Map.Entry.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, !IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEAttribute(getStringIndexMapEntry_Value(), this.getIndex(), "value", null, 0, 1, Map.Entry.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, !IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEClass(inputRecipeEClass, InputRecipe.class, "InputRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEAttribute(getInputRecipe_InputKey(), ecorePackage.getEJavaObject(), "inputKey", null, 0, 1, InputRecipe.class, IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEAttribute(getInputRecipe_KeyID(), ecorePackage.getEString(), "keyID", null, 0, 1, InputRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, !IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEAttribute(getInputRecipe_KeyArity(), ecorePackage.getEInt(), "keyArity", null, 0, 1, InputRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEOperation(getInputRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(constantRecipeEClass, ConstantRecipe.class, "ConstantRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEAttribute(getConstantRecipe_ConstantValues(), ecorePackage.getEJavaObject(), "constantValues", null, 0, -1, ConstantRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, !IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEOperation(getConstantRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(transitiveClosureRecipeEClass, TransitiveClosureRecipe.class, "TransitiveClosureRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$

		initEOperation(getTransitiveClosureRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(filterRecipeEClass, FilterRecipe.class, "FilterRecipe", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$

		initEOperation(getFilterRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(inequalityFilterRecipeEClass, InequalityFilterRecipe.class, "InequalityFilterRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEAttribute(getInequalityFilterRecipe_Subject(), this.getIndex(), "subject", null, 0, 1, InequalityFilterRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, !IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEAttribute(getInequalityFilterRecipe_Inequals(), this.getIndex(), "inequals", null, 0, -1, InequalityFilterRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, !IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEClass(equalityFilterRecipeEClass, EqualityFilterRecipe.class, "EqualityFilterRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEAttribute(getEqualityFilterRecipe_Indices(), this.getIndex(), "indices", null, 0, -1, EqualityFilterRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, !IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEClass(transparentRecipeEClass, TransparentRecipe.class, "TransparentRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$

		initEClass(trimmerRecipeEClass, TrimmerRecipe.class, "TrimmerRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEReference(getTrimmerRecipe_Mask(), this.getMask(), null, "mask", null, 0, 1, TrimmerRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEOperation(getTrimmerRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(expressionDefinitionEClass, ExpressionDefinition.class, "ExpressionDefinition", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEAttribute(getExpressionDefinition_Evaluator(), ecorePackage.getEJavaObject(), "evaluator", null, 0, 1, ExpressionDefinition.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, !IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEClass(expressionEnforcerRecipeEClass, ExpressionEnforcerRecipe.class, "ExpressionEnforcerRecipe", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEReference(getExpressionEnforcerRecipe_Expression(), this.getExpressionDefinition(), null, "expression", null, 0, 1, ExpressionEnforcerRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEReference(getExpressionEnforcerRecipe_MappedIndices(), this.getStringIndexMapEntry(), null, "mappedIndices", null, 0, -1, ExpressionEnforcerRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEAttribute(getExpressionEnforcerRecipe_CacheOutput(), ecorePackage.getEBoolean(), "cacheOutput", null, 0, 1, ExpressionEnforcerRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEClass(checkRecipeEClass, CheckRecipe.class, "CheckRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$

		initEOperation(getCheckRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(evalRecipeEClass, EvalRecipe.class, "EvalRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEAttribute(getEvalRecipe_Unwinding(), ecorePackage.getEBoolean(), "unwinding", null, 0, 1, EvalRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEOperation(getEvalRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(indexerBasedAggregatorRecipeEClass, IndexerBasedAggregatorRecipe.class, "IndexerBasedAggregatorRecipe", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEReference(getIndexerBasedAggregatorRecipe_Parent(), this.getProjectionIndexerRecipe(), null, "parent", null, 0, 1, IndexerBasedAggregatorRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEOperation(getIndexerBasedAggregatorRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(countAggregatorRecipeEClass, CountAggregatorRecipe.class, "CountAggregatorRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$

		initEClass(joinRecipeEClass, JoinRecipe.class, "JoinRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEReference(getJoinRecipe_RightParentComplementaryMask(), this.getMask(), null, "rightParentComplementaryMask", null, 0, 1, JoinRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEOperation(getJoinRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(existenceJoinRecipeEClass, ExistenceJoinRecipe.class, "ExistenceJoinRecipe", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$

		initEOperation(getExistenceJoinRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(semiJoinRecipeEClass, SemiJoinRecipe.class, "SemiJoinRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$

		initEClass(antiJoinRecipeEClass, AntiJoinRecipe.class, "AntiJoinRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$

		initEClass(inputFilterRecipeEClass, InputFilterRecipe.class, "InputFilterRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEAttribute(getInputFilterRecipe_InputKey(), ecorePackage.getEJavaObject(), "inputKey", null, 0, 1, InputFilterRecipe.class, IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEAttribute(getInputFilterRecipe_KeyID(), ecorePackage.getEString(), "keyID", null, 0, 1, InputFilterRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, !IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEReference(getInputFilterRecipe_Mask(), this.getMask(), null, "mask", null, 0, 1, InputFilterRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEClass(singleColumnAggregatorRecipeEClass, SingleColumnAggregatorRecipe.class, "SingleColumnAggregatorRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEAttribute(getSingleColumnAggregatorRecipe_MultisetAggregationOperator(), this.getAggregationOperator(), "multisetAggregationOperator", null, 0, 1, SingleColumnAggregatorRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEAttribute(getSingleColumnAggregatorRecipe_AggregableIndex(), ecorePackage.getEInt(), "aggregableIndex", null, 0, 1, SingleColumnAggregatorRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEReference(getSingleColumnAggregatorRecipe_GroupByMask(), this.getMask(), null, "groupByMask", null, 1, 1, SingleColumnAggregatorRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEOperation(getSingleColumnAggregatorRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(discriminatorDispatcherRecipeEClass, DiscriminatorDispatcherRecipe.class, "DiscriminatorDispatcherRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEAttribute(getDiscriminatorDispatcherRecipe_DiscriminationColumnIndex(), ecorePackage.getEInt(), "discriminationColumnIndex", null, 0, 1, DiscriminatorDispatcherRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEOperation(getDiscriminatorDispatcherRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(discriminatorBucketRecipeEClass, DiscriminatorBucketRecipe.class, "DiscriminatorBucketRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEAttribute(getDiscriminatorBucketRecipe_BucketKey(), ecorePackage.getEJavaObject(), "bucketKey", null, 0, 1, DiscriminatorBucketRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEOperation(getDiscriminatorBucketRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(rederivableNodeRecipeEClass, RederivableNodeRecipe.class, "RederivableNodeRecipe", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEAttribute(getRederivableNodeRecipe_DeleteRederiveEvaluation(), ecorePackage.getEBoolean(), "deleteRederiveEvaluation", "false", 0, 1, RederivableNodeRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$ //$NON-NLS-2$
		initEReference(getRederivableNodeRecipe_OptionalMonotonicityInfo(), this.getMonotonicityInfo(), null, "optionalMonotonicityInfo", null, 0, 1, RederivableNodeRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEClass(relationEvaluationRecipeEClass, RelationEvaluationRecipe.class, "RelationEvaluationRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEReference(getRelationEvaluationRecipe_Evaluator(), this.getExpressionDefinition(), null, "evaluator", null, 0, 1, RelationEvaluationRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEClass(representativeElectionRecipeEClass, RepresentativeElectionRecipe.class, "RepresentativeElectionRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEAttribute(getRepresentativeElectionRecipe_Connectivity(), this.getConnectivity(), "connectivity", null, 0, 1, RepresentativeElectionRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEOperation(getRepresentativeElectionRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(outerJoinNodeRecipeEClass, OuterJoinNodeRecipe.class, "OuterJoinNodeRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEReference(getOuterJoinNodeRecipe_Parent(), this.getProjectionIndexerRecipe(), null, "parent", null, 0, 1, OuterJoinNodeRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$
		initEAttribute(getOuterJoinNodeRecipe_DefaultValue(), ecorePackage.getEJavaObject(), "defaultValue", null, 0, 1, OuterJoinNodeRecipe.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED); //$NON-NLS-1$

		initEOperation(getOuterJoinNodeRecipe__GetArity(), ecorePackage.getEInt(), "getArity", 0, 1, !IS_UNIQUE, IS_ORDERED); //$NON-NLS-1$

		initEClass(outerJoinIndexerRecipeEClass, OuterJoinIndexerRecipe.class, "OuterJoinIndexerRecipe", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$

		// Initialize data types
		initEDataType(indexEDataType, Integer.class, "Index", IS_SERIALIZABLE, !IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$
		initEDataType(aggregationOperatorEDataType, IMultisetAggregationOperator.class, "AggregationOperator", IS_SERIALIZABLE, !IS_GENERATED_INSTANCE_CLASS, "tools.refinery.interpreter.matchers.psystem.aggregations.IMultisetAggregationOperator<?, ?, ?>"); //$NON-NLS-1$ //$NON-NLS-2$
		initEDataType(connectivityEDataType, Connectivity.class, "Connectivity", IS_SERIALIZABLE, !IS_GENERATED_INSTANCE_CLASS); //$NON-NLS-1$

		// Create resource
		createResource(eNS_URI);
	}

} //RecipesPackageImpl
