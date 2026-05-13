/**
 */
package tools.refinery.language.model.problem.impl;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EDataType;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;

import org.eclipse.emf.ecore.impl.EFactoryImpl;

import org.eclipse.emf.ecore.plugin.EcorePlugin;

import tools.refinery.language.model.problem.*;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model <b>Factory</b>.
 * <!-- end-user-doc -->
 * @generated
 */
public class ProblemFactoryImpl extends EFactoryImpl implements ProblemFactory
{
	/**
	 * Creates the default factory implementation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static ProblemFactory init()
	{
		try
		{
			ProblemFactory theProblemFactory = (ProblemFactory)EPackage.Registry.INSTANCE.getEFactory(ProblemPackage.eNS_URI);
			if (theProblemFactory != null)
			{
				return theProblemFactory;
			}
		}
		catch (Exception exception)
		{
			EcorePlugin.INSTANCE.log(exception);
		}
		return new ProblemFactoryImpl();
	}

	/**
	 * Creates an instance of the factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ProblemFactoryImpl()
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
			case ProblemPackage.PROBLEM: return createProblem();
			case ProblemPackage.CLASS_DECLARATION: return createClassDeclaration();
			case ProblemPackage.REFERENCE_DECLARATION: return createReferenceDeclaration();
			case ProblemPackage.PREDICATE_DEFINITION: return createPredicateDefinition();
			case ProblemPackage.PARAMETER: return createParameter();
			case ProblemPackage.ATOM: return createAtom();
			case ProblemPackage.IMPLICIT_VARIABLE: return createImplicitVariable();
			case ProblemPackage.NODE: return createNode();
			case ProblemPackage.SCOPE_DECLARATION: return createScopeDeclaration();
			case ProblemPackage.TYPE_SCOPE: return createTypeScope();
			case ProblemPackage.RANGE_MULTIPLICITY: return createRangeMultiplicity();
			case ProblemPackage.EXACT_MULTIPLICITY: return createExactMultiplicity();
			case ProblemPackage.UNBOUNDED_MULTIPLICITY: return createUnboundedMultiplicity();
			case ProblemPackage.ENUM_DECLARATION: return createEnumDeclaration();
			case ProblemPackage.INT_CONSTANT: return createIntConstant();
			case ProblemPackage.REAL_CONSTANT: return createRealConstant();
			case ProblemPackage.STRING_CONSTANT: return createStringConstant();
			case ProblemPackage.NODE_ASSERTION_ARGUMENT: return createNodeAssertionArgument();
			case ProblemPackage.NODE_DECLARATION: return createNodeDeclaration();
			case ProblemPackage.WILDCARD_ASSERTION_ARGUMENT: return createWildcardAssertionArgument();
			case ProblemPackage.RULE_DEFINITION: return createRuleDefinition();
			case ProblemPackage.CONSEQUENT: return createConsequent();
			case ProblemPackage.ASSERTION_ACTION: return createAssertionAction();
			case ProblemPackage.VARIABLE_OR_NODE_EXPR: return createVariableOrNodeExpr();
			case ProblemPackage.ARITHMETIC_UNARY_EXPR: return createArithmeticUnaryExpr();
			case ProblemPackage.AGGREGATION_EXPR: return createAggregationExpr();
			case ProblemPackage.COMPARISON_EXPR: return createComparisonExpr();
			case ProblemPackage.NEGATION_EXPR: return createNegationExpr();
			case ProblemPackage.FUNCTION_DEFINITION: return createFunctionDefinition();
			case ProblemPackage.CONJUNCTION: return createConjunction();
			case ProblemPackage.CASE: return createCase();
			case ProblemPackage.ARITHMETIC_BINARY_EXPR: return createArithmeticBinaryExpr();
			case ProblemPackage.RANGE_EXPR: return createRangeExpr();
			case ProblemPackage.LOGIC_CONSTANT: return createLogicConstant();
			case ProblemPackage.IMPORT_STATEMENT: return createImportStatement();
			case ProblemPackage.DATATYPE_DECLARATION: return createDatatypeDeclaration();
			case ProblemPackage.LATTICE_BINARY_EXPR: return createLatticeBinaryExpr();
			case ProblemPackage.ASSIGNMENT_EXPR: return createAssignmentExpr();
			case ProblemPackage.INFINITE_CONSTANT: return createInfiniteConstant();
			case ProblemPackage.AGGREGATOR_DECLARATION: return createAggregatorDeclaration();
			case ProblemPackage.MODAL_EXPR: return createModalExpr();
			case ProblemPackage.ASSERTION: return createAssertion();
			case ProblemPackage.ANNOTATION_CONTAINER: return createAnnotationContainer();
			case ProblemPackage.ANNOTATION_DECLARATION: return createAnnotationDeclaration();
			case ProblemPackage.ANNOTATION: return createAnnotation();
			case ProblemPackage.ANNOTATION_ARGUMENT: return createAnnotationArgument();
			case ProblemPackage.TOP_LEVEL_ANNOTATION: return createTopLevelAnnotation();
			case ProblemPackage.OVERLOADED_DECLARATION: return createOverloadedDeclaration();
			case ProblemPackage.THEORY_ACTION: return createTheoryAction();
			default:
				throw new IllegalArgumentException("The class '" + eClass.getName() + "' is not a valid classifier");
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
			case ProblemPackage.LOGIC_VALUE:
				return createLogicValueFromString(eDataType, initialValue);
			case ProblemPackage.COMPARISON_OP:
				return createComparisonOpFromString(eDataType, initialValue);
			case ProblemPackage.REFERENCE_KIND:
				return createReferenceKindFromString(eDataType, initialValue);
			case ProblemPackage.UNARY_OP:
				return createUnaryOpFromString(eDataType, initialValue);
			case ProblemPackage.BINARY_OP:
				return createBinaryOpFromString(eDataType, initialValue);
			case ProblemPackage.MODULE_KIND:
				return createModuleKindFromString(eDataType, initialValue);
			case ProblemPackage.NODE_KIND:
				return createNodeKindFromString(eDataType, initialValue);
			case ProblemPackage.LATTICE_BINARY_OP:
				return createLatticeBinaryOpFromString(eDataType, initialValue);
			case ProblemPackage.MODALITY:
				return createModalityFromString(eDataType, initialValue);
			case ProblemPackage.CONCRETENESS:
				return createConcretenessFromString(eDataType, initialValue);
			case ProblemPackage.RULE_KIND:
				return createRuleKindFromString(eDataType, initialValue);
			case ProblemPackage.PREDICATE_KIND:
				return createPredicateKindFromString(eDataType, initialValue);
			case ProblemPackage.PARAMETER_KIND:
				return createParameterKindFromString(eDataType, initialValue);
			default:
				throw new IllegalArgumentException("The datatype '" + eDataType.getName() + "' is not a valid classifier");
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
			case ProblemPackage.LOGIC_VALUE:
				return convertLogicValueToString(eDataType, instanceValue);
			case ProblemPackage.COMPARISON_OP:
				return convertComparisonOpToString(eDataType, instanceValue);
			case ProblemPackage.REFERENCE_KIND:
				return convertReferenceKindToString(eDataType, instanceValue);
			case ProblemPackage.UNARY_OP:
				return convertUnaryOpToString(eDataType, instanceValue);
			case ProblemPackage.BINARY_OP:
				return convertBinaryOpToString(eDataType, instanceValue);
			case ProblemPackage.MODULE_KIND:
				return convertModuleKindToString(eDataType, instanceValue);
			case ProblemPackage.NODE_KIND:
				return convertNodeKindToString(eDataType, instanceValue);
			case ProblemPackage.LATTICE_BINARY_OP:
				return convertLatticeBinaryOpToString(eDataType, instanceValue);
			case ProblemPackage.MODALITY:
				return convertModalityToString(eDataType, instanceValue);
			case ProblemPackage.CONCRETENESS:
				return convertConcretenessToString(eDataType, instanceValue);
			case ProblemPackage.RULE_KIND:
				return convertRuleKindToString(eDataType, instanceValue);
			case ProblemPackage.PREDICATE_KIND:
				return convertPredicateKindToString(eDataType, instanceValue);
			case ProblemPackage.PARAMETER_KIND:
				return convertParameterKindToString(eDataType, instanceValue);
			default:
				throw new IllegalArgumentException("The datatype '" + eDataType.getName() + "' is not a valid classifier");
		}
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Problem createProblem()
	{
		ProblemImpl problem = new ProblemImpl();
		return problem;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ClassDeclaration createClassDeclaration()
	{
		ClassDeclarationImpl classDeclaration = new ClassDeclarationImpl();
		return classDeclaration;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ReferenceDeclaration createReferenceDeclaration()
	{
		ReferenceDeclarationImpl referenceDeclaration = new ReferenceDeclarationImpl();
		return referenceDeclaration;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public PredicateDefinition createPredicateDefinition()
	{
		PredicateDefinitionImpl predicateDefinition = new PredicateDefinitionImpl();
		return predicateDefinition;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Parameter createParameter()
	{
		ParameterImpl parameter = new ParameterImpl();
		return parameter;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Atom createAtom()
	{
		AtomImpl atom = new AtomImpl();
		return atom;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ImplicitVariable createImplicitVariable()
	{
		ImplicitVariableImpl implicitVariable = new ImplicitVariableImpl();
		return implicitVariable;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Node createNode()
	{
		NodeImpl node = new NodeImpl();
		return node;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ScopeDeclaration createScopeDeclaration()
	{
		ScopeDeclarationImpl scopeDeclaration = new ScopeDeclarationImpl();
		return scopeDeclaration;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public TypeScope createTypeScope()
	{
		TypeScopeImpl typeScope = new TypeScopeImpl();
		return typeScope;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public RangeMultiplicity createRangeMultiplicity()
	{
		RangeMultiplicityImpl rangeMultiplicity = new RangeMultiplicityImpl();
		return rangeMultiplicity;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ExactMultiplicity createExactMultiplicity()
	{
		ExactMultiplicityImpl exactMultiplicity = new ExactMultiplicityImpl();
		return exactMultiplicity;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public UnboundedMultiplicity createUnboundedMultiplicity()
	{
		UnboundedMultiplicityImpl unboundedMultiplicity = new UnboundedMultiplicityImpl();
		return unboundedMultiplicity;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EnumDeclaration createEnumDeclaration()
	{
		EnumDeclarationImpl enumDeclaration = new EnumDeclarationImpl();
		return enumDeclaration;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public IntConstant createIntConstant()
	{
		IntConstantImpl intConstant = new IntConstantImpl();
		return intConstant;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public RealConstant createRealConstant()
	{
		RealConstantImpl realConstant = new RealConstantImpl();
		return realConstant;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public StringConstant createStringConstant()
	{
		StringConstantImpl stringConstant = new StringConstantImpl();
		return stringConstant;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NodeAssertionArgument createNodeAssertionArgument()
	{
		NodeAssertionArgumentImpl nodeAssertionArgument = new NodeAssertionArgumentImpl();
		return nodeAssertionArgument;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NodeDeclaration createNodeDeclaration()
	{
		NodeDeclarationImpl nodeDeclaration = new NodeDeclarationImpl();
		return nodeDeclaration;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public WildcardAssertionArgument createWildcardAssertionArgument()
	{
		WildcardAssertionArgumentImpl wildcardAssertionArgument = new WildcardAssertionArgumentImpl();
		return wildcardAssertionArgument;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public RuleDefinition createRuleDefinition()
	{
		RuleDefinitionImpl ruleDefinition = new RuleDefinitionImpl();
		return ruleDefinition;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Consequent createConsequent()
	{
		ConsequentImpl consequent = new ConsequentImpl();
		return consequent;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public AssertionAction createAssertionAction()
	{
		AssertionActionImpl assertionAction = new AssertionActionImpl();
		return assertionAction;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public VariableOrNodeExpr createVariableOrNodeExpr()
	{
		VariableOrNodeExprImpl variableOrNodeExpr = new VariableOrNodeExprImpl();
		return variableOrNodeExpr;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ArithmeticUnaryExpr createArithmeticUnaryExpr()
	{
		ArithmeticUnaryExprImpl arithmeticUnaryExpr = new ArithmeticUnaryExprImpl();
		return arithmeticUnaryExpr;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public AggregationExpr createAggregationExpr()
	{
		AggregationExprImpl aggregationExpr = new AggregationExprImpl();
		return aggregationExpr;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ComparisonExpr createComparisonExpr()
	{
		ComparisonExprImpl comparisonExpr = new ComparisonExprImpl();
		return comparisonExpr;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NegationExpr createNegationExpr()
	{
		NegationExprImpl negationExpr = new NegationExprImpl();
		return negationExpr;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public FunctionDefinition createFunctionDefinition()
	{
		FunctionDefinitionImpl functionDefinition = new FunctionDefinitionImpl();
		return functionDefinition;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Conjunction createConjunction()
	{
		ConjunctionImpl conjunction = new ConjunctionImpl();
		return conjunction;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Case createCase()
	{
		CaseImpl case_ = new CaseImpl();
		return case_;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ArithmeticBinaryExpr createArithmeticBinaryExpr()
	{
		ArithmeticBinaryExprImpl arithmeticBinaryExpr = new ArithmeticBinaryExprImpl();
		return arithmeticBinaryExpr;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public RangeExpr createRangeExpr()
	{
		RangeExprImpl rangeExpr = new RangeExprImpl();
		return rangeExpr;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public LogicConstant createLogicConstant()
	{
		LogicConstantImpl logicConstant = new LogicConstantImpl();
		return logicConstant;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ImportStatement createImportStatement()
	{
		ImportStatementImpl importStatement = new ImportStatementImpl();
		return importStatement;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public DatatypeDeclaration createDatatypeDeclaration()
	{
		DatatypeDeclarationImpl datatypeDeclaration = new DatatypeDeclarationImpl();
		return datatypeDeclaration;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public LatticeBinaryExpr createLatticeBinaryExpr()
	{
		LatticeBinaryExprImpl latticeBinaryExpr = new LatticeBinaryExprImpl();
		return latticeBinaryExpr;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public AssignmentExpr createAssignmentExpr()
	{
		AssignmentExprImpl assignmentExpr = new AssignmentExprImpl();
		return assignmentExpr;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public InfiniteConstant createInfiniteConstant()
	{
		InfiniteConstantImpl infiniteConstant = new InfiniteConstantImpl();
		return infiniteConstant;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public AggregatorDeclaration createAggregatorDeclaration()
	{
		AggregatorDeclarationImpl aggregatorDeclaration = new AggregatorDeclarationImpl();
		return aggregatorDeclaration;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ModalExpr createModalExpr()
	{
		ModalExprImpl modalExpr = new ModalExprImpl();
		return modalExpr;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Assertion createAssertion()
	{
		AssertionImpl assertion = new AssertionImpl();
		return assertion;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public AnnotationContainer createAnnotationContainer()
	{
		AnnotationContainerImpl annotationContainer = new AnnotationContainerImpl();
		return annotationContainer;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public AnnotationDeclaration createAnnotationDeclaration()
	{
		AnnotationDeclarationImpl annotationDeclaration = new AnnotationDeclarationImpl();
		return annotationDeclaration;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Annotation createAnnotation()
	{
		AnnotationImpl annotation = new AnnotationImpl();
		return annotation;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public AnnotationArgument createAnnotationArgument()
	{
		AnnotationArgumentImpl annotationArgument = new AnnotationArgumentImpl();
		return annotationArgument;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public TopLevelAnnotation createTopLevelAnnotation()
	{
		TopLevelAnnotationImpl topLevelAnnotation = new TopLevelAnnotationImpl();
		return topLevelAnnotation;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public OverloadedDeclaration createOverloadedDeclaration()
	{
		OverloadedDeclarationImpl overloadedDeclaration = new OverloadedDeclarationImpl();
		return overloadedDeclaration;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public TheoryAction createTheoryAction()
	{
		TheoryActionImpl theoryAction = new TheoryActionImpl();
		return theoryAction;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public LogicValue createLogicValueFromString(EDataType eDataType, String initialValue)
	{
		LogicValue result = LogicValue.get(initialValue);
		if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertLogicValueToString(EDataType eDataType, Object instanceValue)
	{
		return instanceValue == null ? null : instanceValue.toString();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ComparisonOp createComparisonOpFromString(EDataType eDataType, String initialValue)
	{
		ComparisonOp result = ComparisonOp.get(initialValue);
		if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertComparisonOpToString(EDataType eDataType, Object instanceValue)
	{
		return instanceValue == null ? null : instanceValue.toString();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ReferenceKind createReferenceKindFromString(EDataType eDataType, String initialValue)
	{
		ReferenceKind result = ReferenceKind.get(initialValue);
		if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertReferenceKindToString(EDataType eDataType, Object instanceValue)
	{
		return instanceValue == null ? null : instanceValue.toString();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public UnaryOp createUnaryOpFromString(EDataType eDataType, String initialValue)
	{
		UnaryOp result = UnaryOp.get(initialValue);
		if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertUnaryOpToString(EDataType eDataType, Object instanceValue)
	{
		return instanceValue == null ? null : instanceValue.toString();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public BinaryOp createBinaryOpFromString(EDataType eDataType, String initialValue)
	{
		BinaryOp result = BinaryOp.get(initialValue);
		if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertBinaryOpToString(EDataType eDataType, Object instanceValue)
	{
		return instanceValue == null ? null : instanceValue.toString();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ModuleKind createModuleKindFromString(EDataType eDataType, String initialValue)
	{
		ModuleKind result = ModuleKind.get(initialValue);
		if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertModuleKindToString(EDataType eDataType, Object instanceValue)
	{
		return instanceValue == null ? null : instanceValue.toString();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NodeKind createNodeKindFromString(EDataType eDataType, String initialValue)
	{
		NodeKind result = NodeKind.get(initialValue);
		if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertNodeKindToString(EDataType eDataType, Object instanceValue)
	{
		return instanceValue == null ? null : instanceValue.toString();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public LatticeBinaryOp createLatticeBinaryOpFromString(EDataType eDataType, String initialValue)
	{
		LatticeBinaryOp result = LatticeBinaryOp.get(initialValue);
		if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertLatticeBinaryOpToString(EDataType eDataType, Object instanceValue)
	{
		return instanceValue == null ? null : instanceValue.toString();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Modality createModalityFromString(EDataType eDataType, String initialValue)
	{
		Modality result = Modality.get(initialValue);
		if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertModalityToString(EDataType eDataType, Object instanceValue)
	{
		return instanceValue == null ? null : instanceValue.toString();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Concreteness createConcretenessFromString(EDataType eDataType, String initialValue)
	{
		Concreteness result = Concreteness.get(initialValue);
		if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertConcretenessToString(EDataType eDataType, Object instanceValue)
	{
		return instanceValue == null ? null : instanceValue.toString();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public RuleKind createRuleKindFromString(EDataType eDataType, String initialValue)
	{
		RuleKind result = RuleKind.get(initialValue);
		if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertRuleKindToString(EDataType eDataType, Object instanceValue)
	{
		return instanceValue == null ? null : instanceValue.toString();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public PredicateKind createPredicateKindFromString(EDataType eDataType, String initialValue)
	{
		PredicateKind result = PredicateKind.get(initialValue);
		if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertPredicateKindToString(EDataType eDataType, Object instanceValue)
	{
		return instanceValue == null ? null : instanceValue.toString();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ParameterKind createParameterKindFromString(EDataType eDataType, String initialValue)
	{
		ParameterKind result = ParameterKind.get(initialValue);
		if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertParameterKindToString(EDataType eDataType, Object instanceValue)
	{
		return instanceValue == null ? null : instanceValue.toString();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ProblemPackage getProblemPackage()
	{
		return (ProblemPackage)getEPackage();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @deprecated
	 * @generated
	 */
	@Deprecated
	public static ProblemPackage getPackage()
	{
		return ProblemPackage.eINSTANCE;
	}

} //ProblemFactoryImpl
