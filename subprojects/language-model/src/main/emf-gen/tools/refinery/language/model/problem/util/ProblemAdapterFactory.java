/**
 */
package tools.refinery.language.model.problem.util;

import org.eclipse.emf.common.notify.Adapter;
import org.eclipse.emf.common.notify.Notifier;

import org.eclipse.emf.common.notify.impl.AdapterFactoryImpl;

import org.eclipse.emf.ecore.EObject;

import tools.refinery.language.model.problem.*;

/**
 * <!-- begin-user-doc -->
 * The <b>Adapter Factory</b> for the model.
 * It provides an adapter <code>createXXX</code> method for each class of the model.
 * <!-- end-user-doc -->
 * @see tools.refinery.language.model.problem.ProblemPackage
 * @generated
 */
public class ProblemAdapterFactory extends AdapterFactoryImpl
{
	/**
	 * The cached model package.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected static ProblemPackage modelPackage;

	/**
	 * Creates an instance of the adapter factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ProblemAdapterFactory()
	{
		if (modelPackage == null)
		{
			modelPackage = ProblemPackage.eINSTANCE;
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
	protected ProblemSwitch<Adapter> modelSwitch =
		new ProblemSwitch<Adapter>()
		{
			@Override
			public Adapter caseProblem(Problem object)
			{
				return createProblemAdapter();
			}
			@Override
			public Adapter caseClassDeclaration(ClassDeclaration object)
			{
				return createClassDeclarationAdapter();
			}
			@Override
			public Adapter caseReferenceDeclaration(ReferenceDeclaration object)
			{
				return createReferenceDeclarationAdapter();
			}
			@Override
			public Adapter caseNamedElement(NamedElement object)
			{
				return createNamedElementAdapter();
			}
			@Override
			public Adapter casePredicateDefinition(PredicateDefinition object)
			{
				return createPredicateDefinitionAdapter();
			}
			@Override
			public Adapter caseParameter(Parameter object)
			{
				return createParameterAdapter();
			}
			@Override
			public Adapter caseVariable(Variable object)
			{
				return createVariableAdapter();
			}
			@Override
			public Adapter caseAtom(Atom object)
			{
				return createAtomAdapter();
			}
			@Override
			public Adapter caseImplicitVariable(ImplicitVariable object)
			{
				return createImplicitVariableAdapter();
			}
			@Override
			public Adapter caseExistentialQuantifier(ExistentialQuantifier object)
			{
				return createExistentialQuantifierAdapter();
			}
			@Override
			public Adapter caseAbstractAssertion(AbstractAssertion object)
			{
				return createAbstractAssertionAdapter();
			}
			@Override
			public Adapter caseNode(Node object)
			{
				return createNodeAdapter();
			}
			@Override
			public Adapter caseScopeDeclaration(ScopeDeclaration object)
			{
				return createScopeDeclarationAdapter();
			}
			@Override
			public Adapter caseStatement(Statement object)
			{
				return createStatementAdapter();
			}
			@Override
			public Adapter caseTypeScope(TypeScope object)
			{
				return createTypeScopeAdapter();
			}
			@Override
			public Adapter caseMultiplicity(Multiplicity object)
			{
				return createMultiplicityAdapter();
			}
			@Override
			public Adapter caseRangeMultiplicity(RangeMultiplicity object)
			{
				return createRangeMultiplicityAdapter();
			}
			@Override
			public Adapter caseExactMultiplicity(ExactMultiplicity object)
			{
				return createExactMultiplicityAdapter();
			}
			@Override
			public Adapter caseUnboundedMultiplicity(UnboundedMultiplicity object)
			{
				return createUnboundedMultiplicityAdapter();
			}
			@Override
			public Adapter caseEnumDeclaration(EnumDeclaration object)
			{
				return createEnumDeclarationAdapter();
			}
			@Override
			public Adapter caseVariableOrNode(VariableOrNode object)
			{
				return createVariableOrNodeAdapter();
			}
			@Override
			public Adapter caseConstant(Constant object)
			{
				return createConstantAdapter();
			}
			@Override
			public Adapter caseIntConstant(IntConstant object)
			{
				return createIntConstantAdapter();
			}
			@Override
			public Adapter caseRealConstant(RealConstant object)
			{
				return createRealConstantAdapter();
			}
			@Override
			public Adapter caseStringConstant(StringConstant object)
			{
				return createStringConstantAdapter();
			}
			@Override
			public Adapter caseNodeAssertionArgument(NodeAssertionArgument object)
			{
				return createNodeAssertionArgumentAdapter();
			}
			@Override
			public Adapter caseAssertionArgument(AssertionArgument object)
			{
				return createAssertionArgumentAdapter();
			}
			@Override
			public Adapter caseNodeDeclaration(NodeDeclaration object)
			{
				return createNodeDeclarationAdapter();
			}
			@Override
			public Adapter caseWildcardAssertionArgument(WildcardAssertionArgument object)
			{
				return createWildcardAssertionArgumentAdapter();
			}
			@Override
			public Adapter caseParametricDefinition(ParametricDefinition object)
			{
				return createParametricDefinitionAdapter();
			}
			@Override
			public Adapter caseRuleDefinition(RuleDefinition object)
			{
				return createRuleDefinitionAdapter();
			}
			@Override
			public Adapter caseConsequent(Consequent object)
			{
				return createConsequentAdapter();
			}
			@Override
			public Adapter caseAction(Action object)
			{
				return createActionAdapter();
			}
			@Override
			public Adapter caseAssertionAction(AssertionAction object)
			{
				return createAssertionActionAdapter();
			}
			@Override
			public Adapter caseExpr(Expr object)
			{
				return createExprAdapter();
			}
			@Override
			public Adapter caseVariableOrNodeExpr(VariableOrNodeExpr object)
			{
				return createVariableOrNodeExprAdapter();
			}
			@Override
			public Adapter caseBinaryExpr(BinaryExpr object)
			{
				return createBinaryExprAdapter();
			}
			@Override
			public Adapter caseUnaryExpr(UnaryExpr object)
			{
				return createUnaryExprAdapter();
			}
			@Override
			public Adapter caseArithmeticUnaryExpr(ArithmeticUnaryExpr object)
			{
				return createArithmeticUnaryExprAdapter();
			}
			@Override
			public Adapter caseAggregationExpr(AggregationExpr object)
			{
				return createAggregationExprAdapter();
			}
			@Override
			public Adapter caseComparisonExpr(ComparisonExpr object)
			{
				return createComparisonExprAdapter();
			}
			@Override
			public Adapter caseNegationExpr(NegationExpr object)
			{
				return createNegationExprAdapter();
			}
			@Override
			public Adapter caseFunctionDefinition(FunctionDefinition object)
			{
				return createFunctionDefinitionAdapter();
			}
			@Override
			public Adapter caseConjunction(Conjunction object)
			{
				return createConjunctionAdapter();
			}
			@Override
			public Adapter caseCase(Case object)
			{
				return createCaseAdapter();
			}
			@Override
			public Adapter caseArithmeticBinaryExpr(ArithmeticBinaryExpr object)
			{
				return createArithmeticBinaryExprAdapter();
			}
			@Override
			public Adapter caseRelation(Relation object)
			{
				return createRelationAdapter();
			}
			@Override
			public Adapter caseRangeExpr(RangeExpr object)
			{
				return createRangeExprAdapter();
			}
			@Override
			public Adapter caseLogicConstant(LogicConstant object)
			{
				return createLogicConstantAdapter();
			}
			@Override
			public Adapter caseImportStatement(ImportStatement object)
			{
				return createImportStatementAdapter();
			}
			@Override
			public Adapter caseDatatypeDeclaration(DatatypeDeclaration object)
			{
				return createDatatypeDeclarationAdapter();
			}
			@Override
			public Adapter caseLatticeBinaryExpr(LatticeBinaryExpr object)
			{
				return createLatticeBinaryExprAdapter();
			}
			@Override
			public Adapter caseAssignmentExpr(AssignmentExpr object)
			{
				return createAssignmentExprAdapter();
			}
			@Override
			public Adapter caseInfiniteConstant(InfiniteConstant object)
			{
				return createInfiniteConstantAdapter();
			}
			@Override
			public Adapter caseAggregatorDeclaration(AggregatorDeclaration object)
			{
				return createAggregatorDeclarationAdapter();
			}
			@Override
			public Adapter caseModalExpr(ModalExpr object)
			{
				return createModalExprAdapter();
			}
			@Override
			public Adapter caseAssertion(Assertion object)
			{
				return createAssertionAdapter();
			}
			@Override
			public Adapter caseAnnotatedElement(AnnotatedElement object)
			{
				return createAnnotatedElementAdapter();
			}
			@Override
			public Adapter caseAnnotationContainer(AnnotationContainer object)
			{
				return createAnnotationContainerAdapter();
			}
			@Override
			public Adapter caseAnnotationDeclaration(AnnotationDeclaration object)
			{
				return createAnnotationDeclarationAdapter();
			}
			@Override
			public Adapter caseAnnotation(Annotation object)
			{
				return createAnnotationAdapter();
			}
			@Override
			public Adapter caseAnnotationArgument(AnnotationArgument object)
			{
				return createAnnotationArgumentAdapter();
			}
			@Override
			public Adapter caseTopLevelAnnotation(TopLevelAnnotation object)
			{
				return createTopLevelAnnotationAdapter();
			}
			@Override
			public Adapter caseOverloadedDeclaration(OverloadedDeclaration object)
			{
				return createOverloadedDeclarationAdapter();
			}
			@Override
			public Adapter caseTheoryAction(TheoryAction object)
			{
				return createTheoryActionAdapter();
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
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.Problem <em>Problem</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.Problem
	 * @generated
	 */
	public Adapter createProblemAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.ClassDeclaration <em>Class Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.ClassDeclaration
	 * @generated
	 */
	public Adapter createClassDeclarationAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.ReferenceDeclaration <em>Reference Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.ReferenceDeclaration
	 * @generated
	 */
	public Adapter createReferenceDeclarationAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.NamedElement <em>Named Element</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.NamedElement
	 * @generated
	 */
	public Adapter createNamedElementAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.PredicateDefinition <em>Predicate Definition</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.PredicateDefinition
	 * @generated
	 */
	public Adapter createPredicateDefinitionAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.Parameter <em>Parameter</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.Parameter
	 * @generated
	 */
	public Adapter createParameterAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.Variable <em>Variable</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.Variable
	 * @generated
	 */
	public Adapter createVariableAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.Atom <em>Atom</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.Atom
	 * @generated
	 */
	public Adapter createAtomAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.ImplicitVariable <em>Implicit Variable</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.ImplicitVariable
	 * @generated
	 */
	public Adapter createImplicitVariableAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.ExistentialQuantifier <em>Existential Quantifier</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.ExistentialQuantifier
	 * @generated
	 */
	public Adapter createExistentialQuantifierAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.AbstractAssertion <em>Abstract Assertion</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.AbstractAssertion
	 * @generated
	 */
	public Adapter createAbstractAssertionAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.Node <em>Node</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.Node
	 * @generated
	 */
	public Adapter createNodeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.ScopeDeclaration <em>Scope Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.ScopeDeclaration
	 * @generated
	 */
	public Adapter createScopeDeclarationAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.Statement <em>Statement</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.Statement
	 * @generated
	 */
	public Adapter createStatementAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.TypeScope <em>Type Scope</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.TypeScope
	 * @generated
	 */
	public Adapter createTypeScopeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.Multiplicity <em>Multiplicity</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.Multiplicity
	 * @generated
	 */
	public Adapter createMultiplicityAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.RangeMultiplicity <em>Range Multiplicity</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.RangeMultiplicity
	 * @generated
	 */
	public Adapter createRangeMultiplicityAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.ExactMultiplicity <em>Exact Multiplicity</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.ExactMultiplicity
	 * @generated
	 */
	public Adapter createExactMultiplicityAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.UnboundedMultiplicity <em>Unbounded Multiplicity</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.UnboundedMultiplicity
	 * @generated
	 */
	public Adapter createUnboundedMultiplicityAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.EnumDeclaration <em>Enum Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.EnumDeclaration
	 * @generated
	 */
	public Adapter createEnumDeclarationAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.VariableOrNode <em>Variable Or Node</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.VariableOrNode
	 * @generated
	 */
	public Adapter createVariableOrNodeAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.Constant <em>Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.Constant
	 * @generated
	 */
	public Adapter createConstantAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.IntConstant <em>Int Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.IntConstant
	 * @generated
	 */
	public Adapter createIntConstantAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.RealConstant <em>Real Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.RealConstant
	 * @generated
	 */
	public Adapter createRealConstantAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.StringConstant <em>String Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.StringConstant
	 * @generated
	 */
	public Adapter createStringConstantAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.NodeAssertionArgument <em>Node Assertion Argument</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.NodeAssertionArgument
	 * @generated
	 */
	public Adapter createNodeAssertionArgumentAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.AssertionArgument <em>Assertion Argument</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.AssertionArgument
	 * @generated
	 */
	public Adapter createAssertionArgumentAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.NodeDeclaration <em>Node Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.NodeDeclaration
	 * @generated
	 */
	public Adapter createNodeDeclarationAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.WildcardAssertionArgument <em>Wildcard Assertion Argument</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.WildcardAssertionArgument
	 * @generated
	 */
	public Adapter createWildcardAssertionArgumentAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.ParametricDefinition <em>Parametric Definition</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.ParametricDefinition
	 * @generated
	 */
	public Adapter createParametricDefinitionAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.RuleDefinition <em>Rule Definition</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.RuleDefinition
	 * @generated
	 */
	public Adapter createRuleDefinitionAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.Consequent <em>Consequent</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.Consequent
	 * @generated
	 */
	public Adapter createConsequentAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.Action <em>Action</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.Action
	 * @generated
	 */
	public Adapter createActionAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.AssertionAction <em>Assertion Action</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.AssertionAction
	 * @generated
	 */
	public Adapter createAssertionActionAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.Expr <em>Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.Expr
	 * @generated
	 */
	public Adapter createExprAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.VariableOrNodeExpr <em>Variable Or Node Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.VariableOrNodeExpr
	 * @generated
	 */
	public Adapter createVariableOrNodeExprAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.BinaryExpr <em>Binary Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.BinaryExpr
	 * @generated
	 */
	public Adapter createBinaryExprAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.UnaryExpr <em>Unary Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.UnaryExpr
	 * @generated
	 */
	public Adapter createUnaryExprAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.ArithmeticUnaryExpr <em>Arithmetic Unary Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.ArithmeticUnaryExpr
	 * @generated
	 */
	public Adapter createArithmeticUnaryExprAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.AggregationExpr <em>Aggregation Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.AggregationExpr
	 * @generated
	 */
	public Adapter createAggregationExprAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.ComparisonExpr <em>Comparison Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.ComparisonExpr
	 * @generated
	 */
	public Adapter createComparisonExprAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.NegationExpr <em>Negation Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.NegationExpr
	 * @generated
	 */
	public Adapter createNegationExprAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.FunctionDefinition <em>Function Definition</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.FunctionDefinition
	 * @generated
	 */
	public Adapter createFunctionDefinitionAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.Conjunction <em>Conjunction</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.Conjunction
	 * @generated
	 */
	public Adapter createConjunctionAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.Case <em>Case</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.Case
	 * @generated
	 */
	public Adapter createCaseAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.ArithmeticBinaryExpr <em>Arithmetic Binary Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.ArithmeticBinaryExpr
	 * @generated
	 */
	public Adapter createArithmeticBinaryExprAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.Relation <em>Relation</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.Relation
	 * @generated
	 */
	public Adapter createRelationAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.RangeExpr <em>Range Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.RangeExpr
	 * @generated
	 */
	public Adapter createRangeExprAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.LogicConstant <em>Logic Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.LogicConstant
	 * @generated
	 */
	public Adapter createLogicConstantAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.ImportStatement <em>Import Statement</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.ImportStatement
	 * @generated
	 */
	public Adapter createImportStatementAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.DatatypeDeclaration <em>Datatype Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.DatatypeDeclaration
	 * @generated
	 */
	public Adapter createDatatypeDeclarationAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.LatticeBinaryExpr <em>Lattice Binary Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.LatticeBinaryExpr
	 * @generated
	 */
	public Adapter createLatticeBinaryExprAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.AssignmentExpr <em>Assignment Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.AssignmentExpr
	 * @generated
	 */
	public Adapter createAssignmentExprAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.InfiniteConstant <em>Infinite Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.InfiniteConstant
	 * @generated
	 */
	public Adapter createInfiniteConstantAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.AggregatorDeclaration <em>Aggregator Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.AggregatorDeclaration
	 * @generated
	 */
	public Adapter createAggregatorDeclarationAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.ModalExpr <em>Modal Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.ModalExpr
	 * @generated
	 */
	public Adapter createModalExprAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.Assertion <em>Assertion</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.Assertion
	 * @generated
	 */
	public Adapter createAssertionAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.AnnotatedElement <em>Annotated Element</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.AnnotatedElement
	 * @generated
	 */
	public Adapter createAnnotatedElementAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.AnnotationContainer <em>Annotation Container</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.AnnotationContainer
	 * @generated
	 */
	public Adapter createAnnotationContainerAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.AnnotationDeclaration <em>Annotation Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.AnnotationDeclaration
	 * @generated
	 */
	public Adapter createAnnotationDeclarationAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.Annotation <em>Annotation</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.Annotation
	 * @generated
	 */
	public Adapter createAnnotationAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.AnnotationArgument <em>Annotation Argument</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.AnnotationArgument
	 * @generated
	 */
	public Adapter createAnnotationArgumentAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.TopLevelAnnotation <em>Top Level Annotation</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.TopLevelAnnotation
	 * @generated
	 */
	public Adapter createTopLevelAnnotationAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.OverloadedDeclaration <em>Overloaded Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.OverloadedDeclaration
	 * @generated
	 */
	public Adapter createOverloadedDeclarationAdapter()
	{
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link tools.refinery.language.model.problem.TheoryAction <em>Theory Action</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see tools.refinery.language.model.problem.TheoryAction
	 * @generated
	 */
	public Adapter createTheoryActionAdapter()
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

} //ProblemAdapterFactory
