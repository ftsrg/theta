/**
 */
package tools.refinery.language.model.problem.impl;

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EEnum;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EReference;

import org.eclipse.emf.ecore.impl.EPackageImpl;

import tools.refinery.language.model.problem.AbstractAssertion;
import tools.refinery.language.model.problem.Action;
import tools.refinery.language.model.problem.AggregationExpr;
import tools.refinery.language.model.problem.AggregatorDeclaration;
import tools.refinery.language.model.problem.AnnotatedElement;
import tools.refinery.language.model.problem.Annotation;
import tools.refinery.language.model.problem.AnnotationArgument;
import tools.refinery.language.model.problem.AnnotationContainer;
import tools.refinery.language.model.problem.AnnotationDeclaration;
import tools.refinery.language.model.problem.ArithmeticBinaryExpr;
import tools.refinery.language.model.problem.ArithmeticUnaryExpr;
import tools.refinery.language.model.problem.Assertion;
import tools.refinery.language.model.problem.AssertionAction;
import tools.refinery.language.model.problem.AssertionArgument;
import tools.refinery.language.model.problem.AssignmentExpr;
import tools.refinery.language.model.problem.Atom;
import tools.refinery.language.model.problem.BinaryExpr;
import tools.refinery.language.model.problem.BinaryOp;
import tools.refinery.language.model.problem.Case;
import tools.refinery.language.model.problem.ClassDeclaration;
import tools.refinery.language.model.problem.ComparisonExpr;
import tools.refinery.language.model.problem.ComparisonOp;
import tools.refinery.language.model.problem.Concreteness;
import tools.refinery.language.model.problem.Conjunction;
import tools.refinery.language.model.problem.Consequent;
import tools.refinery.language.model.problem.Constant;
import tools.refinery.language.model.problem.DatatypeDeclaration;
import tools.refinery.language.model.problem.EnumDeclaration;
import tools.refinery.language.model.problem.ExactMultiplicity;
import tools.refinery.language.model.problem.ExistentialQuantifier;
import tools.refinery.language.model.problem.Expr;
import tools.refinery.language.model.problem.FunctionDefinition;
import tools.refinery.language.model.problem.ImplicitVariable;
import tools.refinery.language.model.problem.ImportStatement;
import tools.refinery.language.model.problem.InfiniteConstant;
import tools.refinery.language.model.problem.IntConstant;
import tools.refinery.language.model.problem.LatticeBinaryExpr;
import tools.refinery.language.model.problem.LatticeBinaryOp;
import tools.refinery.language.model.problem.LogicConstant;
import tools.refinery.language.model.problem.LogicValue;
import tools.refinery.language.model.problem.ModalExpr;
import tools.refinery.language.model.problem.Modality;
import tools.refinery.language.model.problem.ModuleKind;
import tools.refinery.language.model.problem.Multiplicity;
import tools.refinery.language.model.problem.NamedElement;
import tools.refinery.language.model.problem.NegationExpr;
import tools.refinery.language.model.problem.Node;
import tools.refinery.language.model.problem.NodeAssertionArgument;
import tools.refinery.language.model.problem.NodeDeclaration;
import tools.refinery.language.model.problem.NodeKind;
import tools.refinery.language.model.problem.OverloadedDeclaration;
import tools.refinery.language.model.problem.Parameter;
import tools.refinery.language.model.problem.ParameterKind;
import tools.refinery.language.model.problem.ParametricDefinition;
import tools.refinery.language.model.problem.PredicateDefinition;
import tools.refinery.language.model.problem.PredicateKind;
import tools.refinery.language.model.problem.Problem;
import tools.refinery.language.model.problem.ProblemFactory;
import tools.refinery.language.model.problem.ProblemPackage;
import tools.refinery.language.model.problem.RangeExpr;
import tools.refinery.language.model.problem.RangeMultiplicity;
import tools.refinery.language.model.problem.RealConstant;
import tools.refinery.language.model.problem.ReferenceDeclaration;
import tools.refinery.language.model.problem.ReferenceKind;
import tools.refinery.language.model.problem.Relation;
import tools.refinery.language.model.problem.RuleDefinition;
import tools.refinery.language.model.problem.RuleKind;
import tools.refinery.language.model.problem.ScopeDeclaration;
import tools.refinery.language.model.problem.Statement;
import tools.refinery.language.model.problem.StringConstant;
import tools.refinery.language.model.problem.TheoryAction;
import tools.refinery.language.model.problem.TopLevelAnnotation;
import tools.refinery.language.model.problem.TypeScope;
import tools.refinery.language.model.problem.UnaryExpr;
import tools.refinery.language.model.problem.UnaryOp;
import tools.refinery.language.model.problem.UnboundedMultiplicity;
import tools.refinery.language.model.problem.Variable;
import tools.refinery.language.model.problem.VariableOrNode;
import tools.refinery.language.model.problem.VariableOrNodeExpr;
import tools.refinery.language.model.problem.WildcardAssertionArgument;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model <b>Package</b>.
 * <!-- end-user-doc -->
 * @generated
 */
public class ProblemPackageImpl extends EPackageImpl implements ProblemPackage
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass problemEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass classDeclarationEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass referenceDeclarationEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass namedElementEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass predicateDefinitionEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass parameterEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass variableEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass atomEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass implicitVariableEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass existentialQuantifierEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass abstractAssertionEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass nodeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass scopeDeclarationEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass statementEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass typeScopeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass multiplicityEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass rangeMultiplicityEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass exactMultiplicityEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass unboundedMultiplicityEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass enumDeclarationEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass variableOrNodeEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass constantEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass intConstantEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass realConstantEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass stringConstantEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass nodeAssertionArgumentEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass assertionArgumentEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass nodeDeclarationEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass wildcardAssertionArgumentEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass parametricDefinitionEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass ruleDefinitionEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass consequentEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass actionEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass assertionActionEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass exprEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass variableOrNodeExprEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass binaryExprEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass unaryExprEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass arithmeticUnaryExprEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass aggregationExprEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass comparisonExprEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass negationExprEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass functionDefinitionEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass conjunctionEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass caseEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass arithmeticBinaryExprEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass relationEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass rangeExprEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass logicConstantEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass importStatementEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass datatypeDeclarationEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass latticeBinaryExprEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass assignmentExprEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass infiniteConstantEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass aggregatorDeclarationEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass modalExprEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass assertionEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass annotatedElementEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass annotationContainerEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass annotationDeclarationEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass annotationEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass annotationArgumentEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass topLevelAnnotationEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass overloadedDeclarationEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass theoryActionEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EEnum logicValueEEnum = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EEnum comparisonOpEEnum = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EEnum referenceKindEEnum = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EEnum unaryOpEEnum = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EEnum binaryOpEEnum = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EEnum moduleKindEEnum = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EEnum nodeKindEEnum = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EEnum latticeBinaryOpEEnum = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EEnum modalityEEnum = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EEnum concretenessEEnum = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EEnum ruleKindEEnum = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EEnum predicateKindEEnum = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EEnum parameterKindEEnum = null;

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
	 * @see tools.refinery.language.model.problem.ProblemPackage#eNS_URI
	 * @see #init()
	 * @generated
	 */
	private ProblemPackageImpl()
	{
		super(eNS_URI, ProblemFactory.eINSTANCE);
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
	 * <p>This method is used to initialize {@link ProblemPackage#eINSTANCE} when that field is accessed.
	 * Clients should not invoke it directly. Instead, they should simply access that field to obtain the package.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #eNS_URI
	 * @see #createPackageContents()
	 * @see #initializePackageContents()
	 * @generated
	 */
	public static ProblemPackage init()
	{
		if (isInited) return (ProblemPackage)EPackage.Registry.INSTANCE.getEPackage(ProblemPackage.eNS_URI);

		// Obtain or create and register package
		Object registeredProblemPackage = EPackage.Registry.INSTANCE.get(eNS_URI);
		ProblemPackageImpl theProblemPackage = registeredProblemPackage instanceof ProblemPackageImpl ? (ProblemPackageImpl)registeredProblemPackage : new ProblemPackageImpl();

		isInited = true;

		// Create package meta-data objects
		theProblemPackage.createPackageContents();

		// Initialize created meta-data
		theProblemPackage.initializePackageContents();

		// Mark meta-data to indicate it can't be changed
		theProblemPackage.freeze();

		// Update the registry and return the package
		EPackage.Registry.INSTANCE.put(ProblemPackage.eNS_URI, theProblemPackage);
		return theProblemPackage;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getProblem()
	{
		return problemEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getProblem_Nodes()
	{
		return (EReference)problemEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getProblem_Statements()
	{
		return (EReference)problemEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getProblem_Kind()
	{
		return (EAttribute)problemEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getProblem_ExplicitKind()
	{
		return (EAttribute)problemEClass.getEStructuralFeatures().get(3);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getClassDeclaration()
	{
		return classDeclarationEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getClassDeclaration_Abstract()
	{
		return (EAttribute)classDeclarationEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getClassDeclaration_FeatureDeclarations()
	{
		return (EReference)classDeclarationEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getClassDeclaration_NewNode()
	{
		return (EReference)classDeclarationEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getClassDeclaration_SuperTypes()
	{
		return (EReference)classDeclarationEClass.getEStructuralFeatures().get(3);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getReferenceDeclaration()
	{
		return referenceDeclarationEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getReferenceDeclaration_Opposite()
	{
		return (EReference)referenceDeclarationEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getReferenceDeclaration_Multiplicity()
	{
		return (EReference)referenceDeclarationEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getReferenceDeclaration_Kind()
	{
		return (EAttribute)referenceDeclarationEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getReferenceDeclaration_ReferenceType()
	{
		return (EReference)referenceDeclarationEClass.getEStructuralFeatures().get(3);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getReferenceDeclaration_InvalidMultiplicity()
	{
		return (EReference)referenceDeclarationEClass.getEStructuralFeatures().get(4);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getReferenceDeclaration_SuperSets()
	{
		return (EReference)referenceDeclarationEClass.getEStructuralFeatures().get(5);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getNamedElement()
	{
		return namedElementEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getNamedElement_Name()
	{
		return (EAttribute)namedElementEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getPredicateDefinition()
	{
		return predicateDefinitionEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getPredicateDefinition_Bodies()
	{
		return (EReference)predicateDefinitionEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getPredicateDefinition_Kind()
	{
		return (EAttribute)predicateDefinitionEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getPredicateDefinition_ComputedValue()
	{
		return (EReference)predicateDefinitionEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getPredicateDefinition_SuperSets()
	{
		return (EReference)predicateDefinitionEClass.getEStructuralFeatures().get(3);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getParameter()
	{
		return parameterEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getParameter_ParameterType()
	{
		return (EReference)parameterEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getParameter_Kind()
	{
		return (EAttribute)parameterEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getVariable()
	{
		return variableEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getAtom()
	{
		return atomEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getAtom_TransitiveClosure()
	{
		return (EAttribute)atomEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getAtom_Arguments()
	{
		return (EReference)atomEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getAtom_Relation()
	{
		return (EReference)atomEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getImplicitVariable()
	{
		return implicitVariableEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getExistentialQuantifier()
	{
		return existentialQuantifierEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getExistentialQuantifier_ImplicitVariables()
	{
		return (EReference)existentialQuantifierEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getAbstractAssertion()
	{
		return abstractAssertionEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getAbstractAssertion_Arguments()
	{
		return (EReference)abstractAssertionEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getAbstractAssertion_Relation()
	{
		return (EReference)abstractAssertionEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getAbstractAssertion_Value()
	{
		return (EReference)abstractAssertionEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getNode()
	{
		return nodeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getScopeDeclaration()
	{
		return scopeDeclarationEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getScopeDeclaration_TypeScopes()
	{
		return (EReference)scopeDeclarationEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getStatement()
	{
		return statementEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getTypeScope()
	{
		return typeScopeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getTypeScope_Increment()
	{
		return (EAttribute)typeScopeEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getTypeScope_Multiplicity()
	{
		return (EReference)typeScopeEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getTypeScope_TargetType()
	{
		return (EReference)typeScopeEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getMultiplicity()
	{
		return multiplicityEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getRangeMultiplicity()
	{
		return rangeMultiplicityEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getRangeMultiplicity_LowerBound()
	{
		return (EAttribute)rangeMultiplicityEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getRangeMultiplicity_UpperBound()
	{
		return (EAttribute)rangeMultiplicityEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getExactMultiplicity()
	{
		return exactMultiplicityEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getExactMultiplicity_ExactValue()
	{
		return (EAttribute)exactMultiplicityEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getUnboundedMultiplicity()
	{
		return unboundedMultiplicityEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getEnumDeclaration()
	{
		return enumDeclarationEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getEnumDeclaration_Literals()
	{
		return (EReference)enumDeclarationEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getVariableOrNode()
	{
		return variableOrNodeEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getConstant()
	{
		return constantEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getIntConstant()
	{
		return intConstantEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getIntConstant_IntValue()
	{
		return (EAttribute)intConstantEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getRealConstant()
	{
		return realConstantEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getRealConstant_RealValue()
	{
		return (EAttribute)realConstantEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getStringConstant()
	{
		return stringConstantEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getStringConstant_StringValue()
	{
		return (EAttribute)stringConstantEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getNodeAssertionArgument()
	{
		return nodeAssertionArgumentEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getNodeAssertionArgument_Node()
	{
		return (EReference)nodeAssertionArgumentEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getAssertionArgument()
	{
		return assertionArgumentEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getNodeDeclaration()
	{
		return nodeDeclarationEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getNodeDeclaration_Nodes()
	{
		return (EReference)nodeDeclarationEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getNodeDeclaration_Kind()
	{
		return (EAttribute)nodeDeclarationEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getWildcardAssertionArgument()
	{
		return wildcardAssertionArgumentEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getParametricDefinition()
	{
		return parametricDefinitionEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getParametricDefinition_Parameters()
	{
		return (EReference)parametricDefinitionEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getRuleDefinition()
	{
		return ruleDefinitionEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getRuleDefinition_Consequents()
	{
		return (EReference)ruleDefinitionEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getRuleDefinition_Preconditions()
	{
		return (EReference)ruleDefinitionEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getRuleDefinition_Kind()
	{
		return (EAttribute)ruleDefinitionEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getConsequent()
	{
		return consequentEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getConsequent_Actions()
	{
		return (EReference)consequentEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getAction()
	{
		return actionEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getAssertionAction()
	{
		return assertionActionEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getExpr()
	{
		return exprEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getVariableOrNodeExpr()
	{
		return variableOrNodeExprEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getVariableOrNodeExpr_VariableOrNode()
	{
		return (EReference)variableOrNodeExprEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getVariableOrNodeExpr_SingletonVariable()
	{
		return (EReference)variableOrNodeExprEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getVariableOrNodeExpr_Relation()
	{
		return (EReference)variableOrNodeExprEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getVariableOrNodeExpr_Element()
	{
		return (EReference)variableOrNodeExprEClass.getEStructuralFeatures().get(3);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getBinaryExpr()
	{
		return binaryExprEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getBinaryExpr_Left()
	{
		return (EReference)binaryExprEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getBinaryExpr_Right()
	{
		return (EReference)binaryExprEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getUnaryExpr()
	{
		return unaryExprEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getUnaryExpr_Body()
	{
		return (EReference)unaryExprEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getArithmeticUnaryExpr()
	{
		return arithmeticUnaryExprEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getArithmeticUnaryExpr_Op()
	{
		return (EAttribute)arithmeticUnaryExprEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getAggregationExpr()
	{
		return aggregationExprEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getAggregationExpr_Value()
	{
		return (EReference)aggregationExprEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getAggregationExpr_Condition()
	{
		return (EReference)aggregationExprEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getAggregationExpr_Aggregator()
	{
		return (EReference)aggregationExprEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getComparisonExpr()
	{
		return comparisonExprEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getComparisonExpr_Op()
	{
		return (EAttribute)comparisonExprEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getNegationExpr()
	{
		return negationExprEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getFunctionDefinition()
	{
		return functionDefinitionEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getFunctionDefinition_Cases()
	{
		return (EReference)functionDefinitionEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getFunctionDefinition_FunctionType()
	{
		return (EReference)functionDefinitionEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getFunctionDefinition_Shadow()
	{
		return (EAttribute)functionDefinitionEClass.getEStructuralFeatures().get(2);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getFunctionDefinition_ComputedValue()
	{
		return (EReference)functionDefinitionEClass.getEStructuralFeatures().get(3);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getFunctionDefinition_DomainPredicate()
	{
		return (EReference)functionDefinitionEClass.getEStructuralFeatures().get(4);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getConjunction()
	{
		return conjunctionEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getConjunction_Literals()
	{
		return (EReference)conjunctionEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getCase()
	{
		return caseEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getCase_Condition()
	{
		return (EReference)caseEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getCase_Value()
	{
		return (EReference)caseEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getArithmeticBinaryExpr()
	{
		return arithmeticBinaryExprEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getArithmeticBinaryExpr_Op()
	{
		return (EAttribute)arithmeticBinaryExprEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getRelation()
	{
		return relationEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getRangeExpr()
	{
		return rangeExprEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getLogicConstant()
	{
		return logicConstantEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getLogicConstant_LogicValue()
	{
		return (EAttribute)logicConstantEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getImportStatement()
	{
		return importStatementEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getImportStatement_ImportedModule()
	{
		return (EReference)importStatementEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getImportStatement_Alias()
	{
		return (EAttribute)importStatementEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getDatatypeDeclaration()
	{
		return datatypeDeclarationEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getLatticeBinaryExpr()
	{
		return latticeBinaryExprEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getLatticeBinaryExpr_Op()
	{
		return (EAttribute)latticeBinaryExprEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getAssignmentExpr()
	{
		return assignmentExprEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getInfiniteConstant()
	{
		return infiniteConstantEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getAggregatorDeclaration()
	{
		return aggregatorDeclarationEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getModalExpr()
	{
		return modalExprEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getModalExpr_Concreteness()
	{
		return (EAttribute)modalExprEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getModalExpr_Modality()
	{
		return (EAttribute)modalExprEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getAssertion()
	{
		return assertionEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getAssertion_Default()
	{
		return (EAttribute)assertionEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getAnnotatedElement()
	{
		return annotatedElementEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getAnnotatedElement_Annotations()
	{
		return (EReference)annotatedElementEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getAnnotationContainer()
	{
		return annotationContainerEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getAnnotationContainer_Annotations()
	{
		return (EReference)annotationContainerEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getAnnotationDeclaration()
	{
		return annotationDeclarationEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getAnnotation()
	{
		return annotationEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getAnnotation_Declaration()
	{
		return (EReference)annotationEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getAnnotation_Arguments()
	{
		return (EReference)annotationEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getAnnotationArgument()
	{
		return annotationArgumentEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getAnnotationArgument_Value()
	{
		return (EReference)annotationArgumentEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getAnnotationArgument_Parameter()
	{
		return (EReference)annotationArgumentEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getTopLevelAnnotation()
	{
		return topLevelAnnotationEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getTopLevelAnnotation_Annotation()
	{
		return (EReference)topLevelAnnotationEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getOverloadedDeclaration()
	{
		return overloadedDeclarationEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getOverloadedDeclaration_Shadow()
	{
		return (EAttribute)overloadedDeclarationEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getTheoryAction()
	{
		return theoryActionEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EReference getTheoryAction_Term()
	{
		return (EReference)theoryActionEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EEnum getLogicValue()
	{
		return logicValueEEnum;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EEnum getComparisonOp()
	{
		return comparisonOpEEnum;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EEnum getReferenceKind()
	{
		return referenceKindEEnum;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EEnum getUnaryOp()
	{
		return unaryOpEEnum;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EEnum getBinaryOp()
	{
		return binaryOpEEnum;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EEnum getModuleKind()
	{
		return moduleKindEEnum;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EEnum getNodeKind()
	{
		return nodeKindEEnum;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EEnum getLatticeBinaryOp()
	{
		return latticeBinaryOpEEnum;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EEnum getModality()
	{
		return modalityEEnum;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EEnum getConcreteness()
	{
		return concretenessEEnum;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EEnum getRuleKind()
	{
		return ruleKindEEnum;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EEnum getPredicateKind()
	{
		return predicateKindEEnum;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EEnum getParameterKind()
	{
		return parameterKindEEnum;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ProblemFactory getProblemFactory()
	{
		return (ProblemFactory)getEFactoryInstance();
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
		problemEClass = createEClass(PROBLEM);
		createEReference(problemEClass, PROBLEM__NODES);
		createEReference(problemEClass, PROBLEM__STATEMENTS);
		createEAttribute(problemEClass, PROBLEM__KIND);
		createEAttribute(problemEClass, PROBLEM__EXPLICIT_KIND);

		classDeclarationEClass = createEClass(CLASS_DECLARATION);
		createEAttribute(classDeclarationEClass, CLASS_DECLARATION__ABSTRACT);
		createEReference(classDeclarationEClass, CLASS_DECLARATION__FEATURE_DECLARATIONS);
		createEReference(classDeclarationEClass, CLASS_DECLARATION__NEW_NODE);
		createEReference(classDeclarationEClass, CLASS_DECLARATION__SUPER_TYPES);

		referenceDeclarationEClass = createEClass(REFERENCE_DECLARATION);
		createEReference(referenceDeclarationEClass, REFERENCE_DECLARATION__OPPOSITE);
		createEReference(referenceDeclarationEClass, REFERENCE_DECLARATION__MULTIPLICITY);
		createEAttribute(referenceDeclarationEClass, REFERENCE_DECLARATION__KIND);
		createEReference(referenceDeclarationEClass, REFERENCE_DECLARATION__REFERENCE_TYPE);
		createEReference(referenceDeclarationEClass, REFERENCE_DECLARATION__INVALID_MULTIPLICITY);
		createEReference(referenceDeclarationEClass, REFERENCE_DECLARATION__SUPER_SETS);

		namedElementEClass = createEClass(NAMED_ELEMENT);
		createEAttribute(namedElementEClass, NAMED_ELEMENT__NAME);

		predicateDefinitionEClass = createEClass(PREDICATE_DEFINITION);
		createEReference(predicateDefinitionEClass, PREDICATE_DEFINITION__BODIES);
		createEAttribute(predicateDefinitionEClass, PREDICATE_DEFINITION__KIND);
		createEReference(predicateDefinitionEClass, PREDICATE_DEFINITION__COMPUTED_VALUE);
		createEReference(predicateDefinitionEClass, PREDICATE_DEFINITION__SUPER_SETS);

		parameterEClass = createEClass(PARAMETER);
		createEReference(parameterEClass, PARAMETER__PARAMETER_TYPE);
		createEAttribute(parameterEClass, PARAMETER__KIND);

		variableEClass = createEClass(VARIABLE);

		atomEClass = createEClass(ATOM);
		createEAttribute(atomEClass, ATOM__TRANSITIVE_CLOSURE);
		createEReference(atomEClass, ATOM__ARGUMENTS);
		createEReference(atomEClass, ATOM__RELATION);

		implicitVariableEClass = createEClass(IMPLICIT_VARIABLE);

		existentialQuantifierEClass = createEClass(EXISTENTIAL_QUANTIFIER);
		createEReference(existentialQuantifierEClass, EXISTENTIAL_QUANTIFIER__IMPLICIT_VARIABLES);

		abstractAssertionEClass = createEClass(ABSTRACT_ASSERTION);
		createEReference(abstractAssertionEClass, ABSTRACT_ASSERTION__ARGUMENTS);
		createEReference(abstractAssertionEClass, ABSTRACT_ASSERTION__RELATION);
		createEReference(abstractAssertionEClass, ABSTRACT_ASSERTION__VALUE);

		nodeEClass = createEClass(NODE);

		scopeDeclarationEClass = createEClass(SCOPE_DECLARATION);
		createEReference(scopeDeclarationEClass, SCOPE_DECLARATION__TYPE_SCOPES);

		statementEClass = createEClass(STATEMENT);

		typeScopeEClass = createEClass(TYPE_SCOPE);
		createEAttribute(typeScopeEClass, TYPE_SCOPE__INCREMENT);
		createEReference(typeScopeEClass, TYPE_SCOPE__MULTIPLICITY);
		createEReference(typeScopeEClass, TYPE_SCOPE__TARGET_TYPE);

		multiplicityEClass = createEClass(MULTIPLICITY);

		rangeMultiplicityEClass = createEClass(RANGE_MULTIPLICITY);
		createEAttribute(rangeMultiplicityEClass, RANGE_MULTIPLICITY__LOWER_BOUND);
		createEAttribute(rangeMultiplicityEClass, RANGE_MULTIPLICITY__UPPER_BOUND);

		exactMultiplicityEClass = createEClass(EXACT_MULTIPLICITY);
		createEAttribute(exactMultiplicityEClass, EXACT_MULTIPLICITY__EXACT_VALUE);

		unboundedMultiplicityEClass = createEClass(UNBOUNDED_MULTIPLICITY);

		enumDeclarationEClass = createEClass(ENUM_DECLARATION);
		createEReference(enumDeclarationEClass, ENUM_DECLARATION__LITERALS);

		variableOrNodeEClass = createEClass(VARIABLE_OR_NODE);

		constantEClass = createEClass(CONSTANT);

		intConstantEClass = createEClass(INT_CONSTANT);
		createEAttribute(intConstantEClass, INT_CONSTANT__INT_VALUE);

		realConstantEClass = createEClass(REAL_CONSTANT);
		createEAttribute(realConstantEClass, REAL_CONSTANT__REAL_VALUE);

		stringConstantEClass = createEClass(STRING_CONSTANT);
		createEAttribute(stringConstantEClass, STRING_CONSTANT__STRING_VALUE);

		nodeAssertionArgumentEClass = createEClass(NODE_ASSERTION_ARGUMENT);
		createEReference(nodeAssertionArgumentEClass, NODE_ASSERTION_ARGUMENT__NODE);

		assertionArgumentEClass = createEClass(ASSERTION_ARGUMENT);

		nodeDeclarationEClass = createEClass(NODE_DECLARATION);
		createEReference(nodeDeclarationEClass, NODE_DECLARATION__NODES);
		createEAttribute(nodeDeclarationEClass, NODE_DECLARATION__KIND);

		wildcardAssertionArgumentEClass = createEClass(WILDCARD_ASSERTION_ARGUMENT);

		parametricDefinitionEClass = createEClass(PARAMETRIC_DEFINITION);
		createEReference(parametricDefinitionEClass, PARAMETRIC_DEFINITION__PARAMETERS);

		ruleDefinitionEClass = createEClass(RULE_DEFINITION);
		createEReference(ruleDefinitionEClass, RULE_DEFINITION__CONSEQUENTS);
		createEReference(ruleDefinitionEClass, RULE_DEFINITION__PRECONDITIONS);
		createEAttribute(ruleDefinitionEClass, RULE_DEFINITION__KIND);

		consequentEClass = createEClass(CONSEQUENT);
		createEReference(consequentEClass, CONSEQUENT__ACTIONS);

		actionEClass = createEClass(ACTION);

		assertionActionEClass = createEClass(ASSERTION_ACTION);

		exprEClass = createEClass(EXPR);

		variableOrNodeExprEClass = createEClass(VARIABLE_OR_NODE_EXPR);
		createEReference(variableOrNodeExprEClass, VARIABLE_OR_NODE_EXPR__VARIABLE_OR_NODE);
		createEReference(variableOrNodeExprEClass, VARIABLE_OR_NODE_EXPR__SINGLETON_VARIABLE);
		createEReference(variableOrNodeExprEClass, VARIABLE_OR_NODE_EXPR__RELATION);
		createEReference(variableOrNodeExprEClass, VARIABLE_OR_NODE_EXPR__ELEMENT);

		binaryExprEClass = createEClass(BINARY_EXPR);
		createEReference(binaryExprEClass, BINARY_EXPR__LEFT);
		createEReference(binaryExprEClass, BINARY_EXPR__RIGHT);

		unaryExprEClass = createEClass(UNARY_EXPR);
		createEReference(unaryExprEClass, UNARY_EXPR__BODY);

		arithmeticUnaryExprEClass = createEClass(ARITHMETIC_UNARY_EXPR);
		createEAttribute(arithmeticUnaryExprEClass, ARITHMETIC_UNARY_EXPR__OP);

		aggregationExprEClass = createEClass(AGGREGATION_EXPR);
		createEReference(aggregationExprEClass, AGGREGATION_EXPR__VALUE);
		createEReference(aggregationExprEClass, AGGREGATION_EXPR__CONDITION);
		createEReference(aggregationExprEClass, AGGREGATION_EXPR__AGGREGATOR);

		comparisonExprEClass = createEClass(COMPARISON_EXPR);
		createEAttribute(comparisonExprEClass, COMPARISON_EXPR__OP);

		negationExprEClass = createEClass(NEGATION_EXPR);

		functionDefinitionEClass = createEClass(FUNCTION_DEFINITION);
		createEReference(functionDefinitionEClass, FUNCTION_DEFINITION__CASES);
		createEReference(functionDefinitionEClass, FUNCTION_DEFINITION__FUNCTION_TYPE);
		createEAttribute(functionDefinitionEClass, FUNCTION_DEFINITION__SHADOW);
		createEReference(functionDefinitionEClass, FUNCTION_DEFINITION__COMPUTED_VALUE);
		createEReference(functionDefinitionEClass, FUNCTION_DEFINITION__DOMAIN_PREDICATE);

		conjunctionEClass = createEClass(CONJUNCTION);
		createEReference(conjunctionEClass, CONJUNCTION__LITERALS);

		caseEClass = createEClass(CASE);
		createEReference(caseEClass, CASE__CONDITION);
		createEReference(caseEClass, CASE__VALUE);

		arithmeticBinaryExprEClass = createEClass(ARITHMETIC_BINARY_EXPR);
		createEAttribute(arithmeticBinaryExprEClass, ARITHMETIC_BINARY_EXPR__OP);

		relationEClass = createEClass(RELATION);

		rangeExprEClass = createEClass(RANGE_EXPR);

		logicConstantEClass = createEClass(LOGIC_CONSTANT);
		createEAttribute(logicConstantEClass, LOGIC_CONSTANT__LOGIC_VALUE);

		importStatementEClass = createEClass(IMPORT_STATEMENT);
		createEReference(importStatementEClass, IMPORT_STATEMENT__IMPORTED_MODULE);
		createEAttribute(importStatementEClass, IMPORT_STATEMENT__ALIAS);

		datatypeDeclarationEClass = createEClass(DATATYPE_DECLARATION);

		latticeBinaryExprEClass = createEClass(LATTICE_BINARY_EXPR);
		createEAttribute(latticeBinaryExprEClass, LATTICE_BINARY_EXPR__OP);

		assignmentExprEClass = createEClass(ASSIGNMENT_EXPR);

		infiniteConstantEClass = createEClass(INFINITE_CONSTANT);

		aggregatorDeclarationEClass = createEClass(AGGREGATOR_DECLARATION);

		modalExprEClass = createEClass(MODAL_EXPR);
		createEAttribute(modalExprEClass, MODAL_EXPR__CONCRETENESS);
		createEAttribute(modalExprEClass, MODAL_EXPR__MODALITY);

		assertionEClass = createEClass(ASSERTION);
		createEAttribute(assertionEClass, ASSERTION__DEFAULT);

		annotatedElementEClass = createEClass(ANNOTATED_ELEMENT);
		createEReference(annotatedElementEClass, ANNOTATED_ELEMENT__ANNOTATIONS);

		annotationContainerEClass = createEClass(ANNOTATION_CONTAINER);
		createEReference(annotationContainerEClass, ANNOTATION_CONTAINER__ANNOTATIONS);

		annotationDeclarationEClass = createEClass(ANNOTATION_DECLARATION);

		annotationEClass = createEClass(ANNOTATION);
		createEReference(annotationEClass, ANNOTATION__DECLARATION);
		createEReference(annotationEClass, ANNOTATION__ARGUMENTS);

		annotationArgumentEClass = createEClass(ANNOTATION_ARGUMENT);
		createEReference(annotationArgumentEClass, ANNOTATION_ARGUMENT__VALUE);
		createEReference(annotationArgumentEClass, ANNOTATION_ARGUMENT__PARAMETER);

		topLevelAnnotationEClass = createEClass(TOP_LEVEL_ANNOTATION);
		createEReference(topLevelAnnotationEClass, TOP_LEVEL_ANNOTATION__ANNOTATION);

		overloadedDeclarationEClass = createEClass(OVERLOADED_DECLARATION);
		createEAttribute(overloadedDeclarationEClass, OVERLOADED_DECLARATION__SHADOW);

		theoryActionEClass = createEClass(THEORY_ACTION);
		createEReference(theoryActionEClass, THEORY_ACTION__TERM);

		// Create enums
		logicValueEEnum = createEEnum(LOGIC_VALUE);
		comparisonOpEEnum = createEEnum(COMPARISON_OP);
		referenceKindEEnum = createEEnum(REFERENCE_KIND);
		unaryOpEEnum = createEEnum(UNARY_OP);
		binaryOpEEnum = createEEnum(BINARY_OP);
		moduleKindEEnum = createEEnum(MODULE_KIND);
		nodeKindEEnum = createEEnum(NODE_KIND);
		latticeBinaryOpEEnum = createEEnum(LATTICE_BINARY_OP);
		modalityEEnum = createEEnum(MODALITY);
		concretenessEEnum = createEEnum(CONCRETENESS);
		ruleKindEEnum = createEEnum(RULE_KIND);
		predicateKindEEnum = createEEnum(PREDICATE_KIND);
		parameterKindEEnum = createEEnum(PARAMETER_KIND);
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
		problemEClass.getESuperTypes().add(this.getNamedElement());
		classDeclarationEClass.getESuperTypes().add(this.getStatement());
		classDeclarationEClass.getESuperTypes().add(this.getRelation());
		classDeclarationEClass.getESuperTypes().add(this.getAnnotatedElement());
		referenceDeclarationEClass.getESuperTypes().add(this.getRelation());
		referenceDeclarationEClass.getESuperTypes().add(this.getAnnotatedElement());
		predicateDefinitionEClass.getESuperTypes().add(this.getParametricDefinition());
		predicateDefinitionEClass.getESuperTypes().add(this.getRelation());
		parameterEClass.getESuperTypes().add(this.getVariable());
		parameterEClass.getESuperTypes().add(this.getAnnotatedElement());
		variableEClass.getESuperTypes().add(this.getVariableOrNode());
		atomEClass.getESuperTypes().add(this.getExpr());
		implicitVariableEClass.getESuperTypes().add(this.getVariable());
		abstractAssertionEClass.getESuperTypes().add(this.getExistentialQuantifier());
		nodeEClass.getESuperTypes().add(this.getVariableOrNode());
		nodeEClass.getESuperTypes().add(this.getAnnotatedElement());
		scopeDeclarationEClass.getESuperTypes().add(this.getStatement());
		rangeMultiplicityEClass.getESuperTypes().add(this.getMultiplicity());
		exactMultiplicityEClass.getESuperTypes().add(this.getMultiplicity());
		unboundedMultiplicityEClass.getESuperTypes().add(this.getMultiplicity());
		enumDeclarationEClass.getESuperTypes().add(this.getStatement());
		enumDeclarationEClass.getESuperTypes().add(this.getRelation());
		enumDeclarationEClass.getESuperTypes().add(this.getAnnotatedElement());
		variableOrNodeEClass.getESuperTypes().add(this.getNamedElement());
		constantEClass.getESuperTypes().add(this.getExpr());
		intConstantEClass.getESuperTypes().add(this.getConstant());
		realConstantEClass.getESuperTypes().add(this.getConstant());
		stringConstantEClass.getESuperTypes().add(this.getConstant());
		nodeAssertionArgumentEClass.getESuperTypes().add(this.getAssertionArgument());
		nodeDeclarationEClass.getESuperTypes().add(this.getStatement());
		nodeDeclarationEClass.getESuperTypes().add(this.getAnnotatedElement());
		wildcardAssertionArgumentEClass.getESuperTypes().add(this.getAssertionArgument());
		parametricDefinitionEClass.getESuperTypes().add(this.getStatement());
		parametricDefinitionEClass.getESuperTypes().add(this.getAnnotatedElement());
		ruleDefinitionEClass.getESuperTypes().add(this.getParametricDefinition());
		ruleDefinitionEClass.getESuperTypes().add(this.getNamedElement());
		assertionActionEClass.getESuperTypes().add(this.getAction());
		assertionActionEClass.getESuperTypes().add(this.getAbstractAssertion());
		variableOrNodeExprEClass.getESuperTypes().add(this.getExpr());
		binaryExprEClass.getESuperTypes().add(this.getExpr());
		unaryExprEClass.getESuperTypes().add(this.getExpr());
		arithmeticUnaryExprEClass.getESuperTypes().add(this.getUnaryExpr());
		aggregationExprEClass.getESuperTypes().add(this.getExpr());
		aggregationExprEClass.getESuperTypes().add(this.getExistentialQuantifier());
		comparisonExprEClass.getESuperTypes().add(this.getBinaryExpr());
		negationExprEClass.getESuperTypes().add(this.getExistentialQuantifier());
		negationExprEClass.getESuperTypes().add(this.getUnaryExpr());
		functionDefinitionEClass.getESuperTypes().add(this.getParametricDefinition());
		functionDefinitionEClass.getESuperTypes().add(this.getRelation());
		conjunctionEClass.getESuperTypes().add(this.getExistentialQuantifier());
		arithmeticBinaryExprEClass.getESuperTypes().add(this.getBinaryExpr());
		relationEClass.getESuperTypes().add(this.getNamedElement());
		rangeExprEClass.getESuperTypes().add(this.getBinaryExpr());
		logicConstantEClass.getESuperTypes().add(this.getConstant());
		importStatementEClass.getESuperTypes().add(this.getStatement());
		datatypeDeclarationEClass.getESuperTypes().add(this.getRelation());
		datatypeDeclarationEClass.getESuperTypes().add(this.getStatement());
		datatypeDeclarationEClass.getESuperTypes().add(this.getAnnotatedElement());
		latticeBinaryExprEClass.getESuperTypes().add(this.getBinaryExpr());
		assignmentExprEClass.getESuperTypes().add(this.getBinaryExpr());
		infiniteConstantEClass.getESuperTypes().add(this.getConstant());
		aggregatorDeclarationEClass.getESuperTypes().add(this.getStatement());
		aggregatorDeclarationEClass.getESuperTypes().add(this.getNamedElement());
		aggregatorDeclarationEClass.getESuperTypes().add(this.getAnnotatedElement());
		modalExprEClass.getESuperTypes().add(this.getUnaryExpr());
		assertionEClass.getESuperTypes().add(this.getStatement());
		assertionEClass.getESuperTypes().add(this.getAbstractAssertion());
		annotationContainerEClass.getESuperTypes().add(this.getStatement());
		annotationDeclarationEClass.getESuperTypes().add(this.getParametricDefinition());
		annotationDeclarationEClass.getESuperTypes().add(this.getNamedElement());
		topLevelAnnotationEClass.getESuperTypes().add(this.getStatement());
		overloadedDeclarationEClass.getESuperTypes().add(this.getParametricDefinition());
		overloadedDeclarationEClass.getESuperTypes().add(this.getRelation());
		theoryActionEClass.getESuperTypes().add(this.getAction());
		theoryActionEClass.getESuperTypes().add(this.getExistentialQuantifier());

		// Initialize classes, features, and operations; add parameters
		initEClass(problemEClass, Problem.class, "Problem", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getProblem_Nodes(), this.getNode(), null, "nodes", null, 0, -1, Problem.class, IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getProblem_Statements(), this.getStatement(), null, "statements", null, 0, -1, Problem.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEAttribute(getProblem_Kind(), this.getModuleKind(), "kind", null, 0, 1, Problem.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEAttribute(getProblem_ExplicitKind(), ecorePackage.getEBoolean(), "explicitKind", null, 0, 1, Problem.class, IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(classDeclarationEClass, ClassDeclaration.class, "ClassDeclaration", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getClassDeclaration_Abstract(), ecorePackage.getEBoolean(), "abstract", null, 0, 1, ClassDeclaration.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getClassDeclaration_FeatureDeclarations(), this.getReferenceDeclaration(), null, "featureDeclarations", null, 0, -1, ClassDeclaration.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getClassDeclaration_NewNode(), this.getNode(), null, "newNode", null, 0, 1, ClassDeclaration.class, IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getClassDeclaration_SuperTypes(), this.getRelation(), null, "superTypes", null, 0, -1, ClassDeclaration.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(referenceDeclarationEClass, ReferenceDeclaration.class, "ReferenceDeclaration", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getReferenceDeclaration_Opposite(), this.getReferenceDeclaration(), null, "opposite", null, 0, 1, ReferenceDeclaration.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getReferenceDeclaration_Multiplicity(), this.getMultiplicity(), null, "multiplicity", null, 0, 1, ReferenceDeclaration.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEAttribute(getReferenceDeclaration_Kind(), this.getReferenceKind(), "kind", null, 0, 1, ReferenceDeclaration.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getReferenceDeclaration_ReferenceType(), this.getRelation(), null, "referenceType", null, 0, 1, ReferenceDeclaration.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getReferenceDeclaration_InvalidMultiplicity(), this.getRelation(), null, "invalidMultiplicity", null, 0, 1, ReferenceDeclaration.class, IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getReferenceDeclaration_SuperSets(), this.getRelation(), null, "superSets", null, 0, -1, ReferenceDeclaration.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(namedElementEClass, NamedElement.class, "NamedElement", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getNamedElement_Name(), ecorePackage.getEString(), "name", null, 0, 1, NamedElement.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(predicateDefinitionEClass, PredicateDefinition.class, "PredicateDefinition", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getPredicateDefinition_Bodies(), this.getConjunction(), null, "bodies", null, 0, -1, PredicateDefinition.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEAttribute(getPredicateDefinition_Kind(), this.getPredicateKind(), "kind", null, 0, 1, PredicateDefinition.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getPredicateDefinition_ComputedValue(), this.getPredicateDefinition(), null, "computedValue", null, 0, 1, PredicateDefinition.class, IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getPredicateDefinition_SuperSets(), this.getRelation(), null, "superSets", null, 0, -1, PredicateDefinition.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(parameterEClass, Parameter.class, "Parameter", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getParameter_ParameterType(), this.getRelation(), null, "parameterType", null, 0, 1, Parameter.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEAttribute(getParameter_Kind(), this.getParameterKind(), "kind", null, 0, 1, Parameter.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(variableEClass, Variable.class, "Variable", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(atomEClass, Atom.class, "Atom", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getAtom_TransitiveClosure(), ecorePackage.getEBoolean(), "transitiveClosure", null, 0, 1, Atom.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getAtom_Arguments(), this.getExpr(), null, "arguments", null, 0, -1, Atom.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getAtom_Relation(), this.getRelation(), null, "relation", null, 0, 1, Atom.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(implicitVariableEClass, ImplicitVariable.class, "ImplicitVariable", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(existentialQuantifierEClass, ExistentialQuantifier.class, "ExistentialQuantifier", IS_ABSTRACT, IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getExistentialQuantifier_ImplicitVariables(), this.getImplicitVariable(), null, "implicitVariables", null, 0, -1, ExistentialQuantifier.class, IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(abstractAssertionEClass, AbstractAssertion.class, "AbstractAssertion", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getAbstractAssertion_Arguments(), this.getAssertionArgument(), null, "arguments", null, 0, -1, AbstractAssertion.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getAbstractAssertion_Relation(), this.getRelation(), null, "relation", null, 0, 1, AbstractAssertion.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getAbstractAssertion_Value(), this.getExpr(), null, "value", null, 0, 1, AbstractAssertion.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(nodeEClass, Node.class, "Node", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(scopeDeclarationEClass, ScopeDeclaration.class, "ScopeDeclaration", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getScopeDeclaration_TypeScopes(), this.getTypeScope(), null, "typeScopes", null, 0, -1, ScopeDeclaration.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(statementEClass, Statement.class, "Statement", IS_ABSTRACT, IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(typeScopeEClass, TypeScope.class, "TypeScope", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getTypeScope_Increment(), ecorePackage.getEBoolean(), "increment", null, 0, 1, TypeScope.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getTypeScope_Multiplicity(), this.getMultiplicity(), null, "multiplicity", null, 0, 1, TypeScope.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getTypeScope_TargetType(), this.getRelation(), null, "targetType", null, 0, 1, TypeScope.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(multiplicityEClass, Multiplicity.class, "Multiplicity", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(rangeMultiplicityEClass, RangeMultiplicity.class, "RangeMultiplicity", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getRangeMultiplicity_LowerBound(), ecorePackage.getEInt(), "lowerBound", "0", 0, 1, RangeMultiplicity.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEAttribute(getRangeMultiplicity_UpperBound(), ecorePackage.getEInt(), "upperBound", "-1", 0, 1, RangeMultiplicity.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(exactMultiplicityEClass, ExactMultiplicity.class, "ExactMultiplicity", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getExactMultiplicity_ExactValue(), ecorePackage.getEInt(), "exactValue", "1", 0, 1, ExactMultiplicity.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(unboundedMultiplicityEClass, UnboundedMultiplicity.class, "UnboundedMultiplicity", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(enumDeclarationEClass, EnumDeclaration.class, "EnumDeclaration", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getEnumDeclaration_Literals(), this.getNode(), null, "literals", null, 0, -1, EnumDeclaration.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(variableOrNodeEClass, VariableOrNode.class, "VariableOrNode", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(constantEClass, Constant.class, "Constant", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(intConstantEClass, IntConstant.class, "IntConstant", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getIntConstant_IntValue(), ecorePackage.getEBigInteger(), "intValue", "0", 0, 1, IntConstant.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(realConstantEClass, RealConstant.class, "RealConstant", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getRealConstant_RealValue(), ecorePackage.getEBigDecimal(), "realValue", "0.0", 0, 1, RealConstant.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(stringConstantEClass, StringConstant.class, "StringConstant", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getStringConstant_StringValue(), ecorePackage.getEString(), "stringValue", null, 0, 1, StringConstant.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(nodeAssertionArgumentEClass, NodeAssertionArgument.class, "NodeAssertionArgument", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getNodeAssertionArgument_Node(), this.getVariableOrNode(), null, "node", null, 0, 1, NodeAssertionArgument.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(assertionArgumentEClass, AssertionArgument.class, "AssertionArgument", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(nodeDeclarationEClass, NodeDeclaration.class, "NodeDeclaration", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getNodeDeclaration_Nodes(), this.getNode(), null, "nodes", null, 0, -1, NodeDeclaration.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEAttribute(getNodeDeclaration_Kind(), this.getNodeKind(), "kind", null, 0, 1, NodeDeclaration.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(wildcardAssertionArgumentEClass, WildcardAssertionArgument.class, "WildcardAssertionArgument", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(parametricDefinitionEClass, ParametricDefinition.class, "ParametricDefinition", IS_ABSTRACT, IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getParametricDefinition_Parameters(), this.getParameter(), null, "parameters", null, 0, -1, ParametricDefinition.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(ruleDefinitionEClass, RuleDefinition.class, "RuleDefinition", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getRuleDefinition_Consequents(), this.getConsequent(), null, "consequents", null, 0, -1, RuleDefinition.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getRuleDefinition_Preconditions(), this.getConjunction(), null, "preconditions", null, 0, -1, RuleDefinition.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEAttribute(getRuleDefinition_Kind(), this.getRuleKind(), "kind", null, 0, 1, RuleDefinition.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(consequentEClass, Consequent.class, "Consequent", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getConsequent_Actions(), this.getAction(), null, "actions", null, 0, -1, Consequent.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(actionEClass, Action.class, "Action", IS_ABSTRACT, IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(assertionActionEClass, AssertionAction.class, "AssertionAction", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(exprEClass, Expr.class, "Expr", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(variableOrNodeExprEClass, VariableOrNodeExpr.class, "VariableOrNodeExpr", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getVariableOrNodeExpr_VariableOrNode(), this.getVariableOrNode(), null, "variableOrNode", null, 0, 1, VariableOrNodeExpr.class, IS_TRANSIENT, IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, IS_DERIVED, IS_ORDERED);
		initEReference(getVariableOrNodeExpr_SingletonVariable(), this.getImplicitVariable(), null, "singletonVariable", null, 0, 1, VariableOrNodeExpr.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getVariableOrNodeExpr_Relation(), this.getRelation(), null, "relation", null, 0, 1, VariableOrNodeExpr.class, IS_TRANSIENT, IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, IS_DERIVED, IS_ORDERED);
		initEReference(getVariableOrNodeExpr_Element(), this.getNamedElement(), null, "element", null, 0, 1, VariableOrNodeExpr.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(binaryExprEClass, BinaryExpr.class, "BinaryExpr", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getBinaryExpr_Left(), this.getExpr(), null, "left", null, 0, 1, BinaryExpr.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getBinaryExpr_Right(), this.getExpr(), null, "right", null, 0, 1, BinaryExpr.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(unaryExprEClass, UnaryExpr.class, "UnaryExpr", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getUnaryExpr_Body(), this.getExpr(), null, "body", null, 0, 1, UnaryExpr.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(arithmeticUnaryExprEClass, ArithmeticUnaryExpr.class, "ArithmeticUnaryExpr", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getArithmeticUnaryExpr_Op(), this.getUnaryOp(), "op", null, 0, 1, ArithmeticUnaryExpr.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(aggregationExprEClass, AggregationExpr.class, "AggregationExpr", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getAggregationExpr_Value(), this.getExpr(), null, "value", null, 0, 1, AggregationExpr.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getAggregationExpr_Condition(), this.getExpr(), null, "condition", null, 0, 1, AggregationExpr.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getAggregationExpr_Aggregator(), this.getAggregatorDeclaration(), null, "aggregator", null, 0, 1, AggregationExpr.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(comparisonExprEClass, ComparisonExpr.class, "ComparisonExpr", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getComparisonExpr_Op(), this.getComparisonOp(), "op", null, 0, 1, ComparisonExpr.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(negationExprEClass, NegationExpr.class, "NegationExpr", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(functionDefinitionEClass, FunctionDefinition.class, "FunctionDefinition", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getFunctionDefinition_Cases(), this.getCase(), null, "cases", null, 0, -1, FunctionDefinition.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getFunctionDefinition_FunctionType(), this.getRelation(), null, "functionType", null, 0, 1, FunctionDefinition.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEAttribute(getFunctionDefinition_Shadow(), ecorePackage.getEBoolean(), "shadow", null, 0, 1, FunctionDefinition.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getFunctionDefinition_ComputedValue(), this.getFunctionDefinition(), null, "computedValue", null, 0, 1, FunctionDefinition.class, IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getFunctionDefinition_DomainPredicate(), this.getPredicateDefinition(), null, "domainPredicate", null, 0, 1, FunctionDefinition.class, IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(conjunctionEClass, Conjunction.class, "Conjunction", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getConjunction_Literals(), this.getExpr(), null, "literals", null, 0, -1, Conjunction.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(caseEClass, Case.class, "Case", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getCase_Condition(), this.getConjunction(), null, "condition", null, 0, 1, Case.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getCase_Value(), this.getExpr(), null, "value", null, 0, 1, Case.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(arithmeticBinaryExprEClass, ArithmeticBinaryExpr.class, "ArithmeticBinaryExpr", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getArithmeticBinaryExpr_Op(), this.getBinaryOp(), "op", null, 0, 1, ArithmeticBinaryExpr.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(relationEClass, Relation.class, "Relation", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(rangeExprEClass, RangeExpr.class, "RangeExpr", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(logicConstantEClass, LogicConstant.class, "LogicConstant", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getLogicConstant_LogicValue(), this.getLogicValue(), "logicValue", null, 0, 1, LogicConstant.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(importStatementEClass, ImportStatement.class, "ImportStatement", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getImportStatement_ImportedModule(), this.getProblem(), null, "importedModule", null, 0, 1, ImportStatement.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEAttribute(getImportStatement_Alias(), ecorePackage.getEString(), "alias", null, 0, 1, ImportStatement.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(datatypeDeclarationEClass, DatatypeDeclaration.class, "DatatypeDeclaration", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(latticeBinaryExprEClass, LatticeBinaryExpr.class, "LatticeBinaryExpr", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getLatticeBinaryExpr_Op(), this.getLatticeBinaryOp(), "op", null, 0, 1, LatticeBinaryExpr.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(assignmentExprEClass, AssignmentExpr.class, "AssignmentExpr", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(infiniteConstantEClass, InfiniteConstant.class, "InfiniteConstant", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(aggregatorDeclarationEClass, AggregatorDeclaration.class, "AggregatorDeclaration", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(modalExprEClass, ModalExpr.class, "ModalExpr", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getModalExpr_Concreteness(), this.getConcreteness(), "concreteness", null, 0, 1, ModalExpr.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEAttribute(getModalExpr_Modality(), this.getModality(), "modality", null, 0, 1, ModalExpr.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(assertionEClass, Assertion.class, "Assertion", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getAssertion_Default(), ecorePackage.getEBoolean(), "default", "false", 0, 1, Assertion.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(annotatedElementEClass, AnnotatedElement.class, "AnnotatedElement", IS_ABSTRACT, IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getAnnotatedElement_Annotations(), this.getAnnotationContainer(), null, "annotations", null, 0, 1, AnnotatedElement.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(annotationContainerEClass, AnnotationContainer.class, "AnnotationContainer", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getAnnotationContainer_Annotations(), this.getAnnotation(), null, "annotations", null, 0, -1, AnnotationContainer.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(annotationDeclarationEClass, AnnotationDeclaration.class, "AnnotationDeclaration", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

		initEClass(annotationEClass, Annotation.class, "Annotation", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getAnnotation_Declaration(), this.getAnnotationDeclaration(), null, "declaration", null, 0, 1, Annotation.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getAnnotation_Arguments(), this.getAnnotationArgument(), null, "arguments", null, 0, -1, Annotation.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(annotationArgumentEClass, AnnotationArgument.class, "AnnotationArgument", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getAnnotationArgument_Value(), this.getExpr(), null, "value", null, 0, 1, AnnotationArgument.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEReference(getAnnotationArgument_Parameter(), this.getParameter(), null, "parameter", null, 0, 1, AnnotationArgument.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(topLevelAnnotationEClass, TopLevelAnnotation.class, "TopLevelAnnotation", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getTopLevelAnnotation_Annotation(), this.getAnnotation(), null, "annotation", null, 0, 1, TopLevelAnnotation.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(overloadedDeclarationEClass, OverloadedDeclaration.class, "OverloadedDeclaration", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getOverloadedDeclaration_Shadow(), ecorePackage.getEBoolean(), "shadow", null, 0, 1, OverloadedDeclaration.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		initEClass(theoryActionEClass, TheoryAction.class, "TheoryAction", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEReference(getTheoryAction_Term(), this.getExpr(), null, "term", null, 0, 1, TheoryAction.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		// Initialize enums and add enum literals
		initEEnum(logicValueEEnum, LogicValue.class, "LogicValue");
		addEEnumLiteral(logicValueEEnum, LogicValue.TRUE);
		addEEnumLiteral(logicValueEEnum, LogicValue.FALSE);
		addEEnumLiteral(logicValueEEnum, LogicValue.UNKNOWN);
		addEEnumLiteral(logicValueEEnum, LogicValue.ERROR);

		initEEnum(comparisonOpEEnum, ComparisonOp.class, "ComparisonOp");
		addEEnumLiteral(comparisonOpEEnum, ComparisonOp.LESS);
		addEEnumLiteral(comparisonOpEEnum, ComparisonOp.LESS_EQ);
		addEEnumLiteral(comparisonOpEEnum, ComparisonOp.GREATER);
		addEEnumLiteral(comparisonOpEEnum, ComparisonOp.GREATER_EQ);
		addEEnumLiteral(comparisonOpEEnum, ComparisonOp.EQ);
		addEEnumLiteral(comparisonOpEEnum, ComparisonOp.NOT_EQ);

		initEEnum(referenceKindEEnum, ReferenceKind.class, "ReferenceKind");
		addEEnumLiteral(referenceKindEEnum, ReferenceKind.DEFAULT);
		addEEnumLiteral(referenceKindEEnum, ReferenceKind.REFERENCE);
		addEEnumLiteral(referenceKindEEnum, ReferenceKind.CONTAINMENT);
		addEEnumLiteral(referenceKindEEnum, ReferenceKind.CONTAINER);

		initEEnum(unaryOpEEnum, UnaryOp.class, "UnaryOp");
		addEEnumLiteral(unaryOpEEnum, UnaryOp.PLUS);
		addEEnumLiteral(unaryOpEEnum, UnaryOp.MINUS);

		initEEnum(binaryOpEEnum, BinaryOp.class, "BinaryOp");
		addEEnumLiteral(binaryOpEEnum, BinaryOp.ADD);
		addEEnumLiteral(binaryOpEEnum, BinaryOp.SUB);
		addEEnumLiteral(binaryOpEEnum, BinaryOp.MUL);
		addEEnumLiteral(binaryOpEEnum, BinaryOp.DIV);
		addEEnumLiteral(binaryOpEEnum, BinaryOp.POW);
		addEEnumLiteral(binaryOpEEnum, BinaryOp.AND);
		addEEnumLiteral(binaryOpEEnum, BinaryOp.OR);
		addEEnumLiteral(binaryOpEEnum, BinaryOp.XOR);

		initEEnum(moduleKindEEnum, ModuleKind.class, "ModuleKind");
		addEEnumLiteral(moduleKindEEnum, ModuleKind.PROBLEM);
		addEEnumLiteral(moduleKindEEnum, ModuleKind.MODULE);

		initEEnum(nodeKindEEnum, NodeKind.class, "NodeKind");
		addEEnumLiteral(nodeKindEEnum, NodeKind.NODE);
		addEEnumLiteral(nodeKindEEnum, NodeKind.ATOM);
		addEEnumLiteral(nodeKindEEnum, NodeKind.MULTI);

		initEEnum(latticeBinaryOpEEnum, LatticeBinaryOp.class, "LatticeBinaryOp");
		addEEnumLiteral(latticeBinaryOpEEnum, LatticeBinaryOp.MEET);
		addEEnumLiteral(latticeBinaryOpEEnum, LatticeBinaryOp.JOIN);
		addEEnumLiteral(latticeBinaryOpEEnum, LatticeBinaryOp.EQ);
		addEEnumLiteral(latticeBinaryOpEEnum, LatticeBinaryOp.NOT_EQ);
		addEEnumLiteral(latticeBinaryOpEEnum, LatticeBinaryOp.SUBSET);
		addEEnumLiteral(latticeBinaryOpEEnum, LatticeBinaryOp.SUPERSET);

		initEEnum(modalityEEnum, Modality.class, "Modality");
		addEEnumLiteral(modalityEEnum, Modality.UNSPECIFIED);
		addEEnumLiteral(modalityEEnum, Modality.MUST);
		addEEnumLiteral(modalityEEnum, Modality.MAY);

		initEEnum(concretenessEEnum, Concreteness.class, "Concreteness");
		addEEnumLiteral(concretenessEEnum, Concreteness.UNSPECIFIED);
		addEEnumLiteral(concretenessEEnum, Concreteness.PARTIAL);
		addEEnumLiteral(concretenessEEnum, Concreteness.CANDIDATE);

		initEEnum(ruleKindEEnum, RuleKind.class, "RuleKind");
		addEEnumLiteral(ruleKindEEnum, RuleKind.REFINEMENT);
		addEEnumLiteral(ruleKindEEnum, RuleKind.PROPAGATION);
		addEEnumLiteral(ruleKindEEnum, RuleKind.DECISION);
		addEEnumLiteral(ruleKindEEnum, RuleKind.CONCRETIZATION);

		initEEnum(predicateKindEEnum, PredicateKind.class, "PredicateKind");
		addEEnumLiteral(predicateKindEEnum, PredicateKind.DEFAULT);
		addEEnumLiteral(predicateKindEEnum, PredicateKind.ERROR);
		addEEnumLiteral(predicateKindEEnum, PredicateKind.SHADOW);

		initEEnum(parameterKindEEnum, ParameterKind.class, "ParameterKind");
		addEEnumLiteral(parameterKindEEnum, ParameterKind.VALUE);
		addEEnumLiteral(parameterKindEEnum, ParameterKind.PRED);

		// Create resource
		createResource(eNS_URI);

		// Create annotations
		// http://www.eclipse.org/emf/2002/Ecore
		createEcoreAnnotations();
		// https://refinery.tools/emf/2024/ProblemDelegate
		createProblemDelegateAnnotations();
	}

	/**
	 * Initializes the annotations for <b>http://www.eclipse.org/emf/2002/Ecore</b>.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected void createEcoreAnnotations()
	{
		String source = "http://www.eclipse.org/emf/2002/Ecore";
		addAnnotation
		  (this,
		   source,
		   new String[]
		   {
			   "settingDelegates", "https://refinery.tools/emf/2024/ProblemDelegate"
		   });
	}

	/**
	 * Initializes the annotations for <b>https://refinery.tools/emf/2024/ProblemDelegate</b>.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected void createProblemDelegateAnnotations()
	{
		String source = "https://refinery.tools/emf/2024/ProblemDelegate";
		addAnnotation
		  (getVariableOrNodeExpr_VariableOrNode(),
		   source,
		   new String[]
		   {
		   });
		addAnnotation
		  (getVariableOrNodeExpr_Relation(),
		   source,
		   new String[]
		   {
		   });
	}

} //ProblemPackageImpl
