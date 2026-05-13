/**
 */
package tools.refinery.language.model.problem;

import org.eclipse.emf.ecore.EFactory;

/**
 * <!-- begin-user-doc -->
 * The <b>Factory</b> for the model.
 * It provides a create method for each non-abstract class of the model.
 * <!-- end-user-doc -->
 * @see tools.refinery.language.model.problem.ProblemPackage
 * @generated
 */
public interface ProblemFactory extends EFactory
{
	/**
	 * The singleton instance of the factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	ProblemFactory eINSTANCE = tools.refinery.language.model.problem.impl.ProblemFactoryImpl.init();

	/**
	 * Returns a new object of class '<em>Problem</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Problem</em>'.
	 * @generated
	 */
	Problem createProblem();

	/**
	 * Returns a new object of class '<em>Class Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Class Declaration</em>'.
	 * @generated
	 */
	ClassDeclaration createClassDeclaration();

	/**
	 * Returns a new object of class '<em>Reference Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Reference Declaration</em>'.
	 * @generated
	 */
	ReferenceDeclaration createReferenceDeclaration();

	/**
	 * Returns a new object of class '<em>Predicate Definition</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Predicate Definition</em>'.
	 * @generated
	 */
	PredicateDefinition createPredicateDefinition();

	/**
	 * Returns a new object of class '<em>Parameter</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Parameter</em>'.
	 * @generated
	 */
	Parameter createParameter();

	/**
	 * Returns a new object of class '<em>Atom</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Atom</em>'.
	 * @generated
	 */
	Atom createAtom();

	/**
	 * Returns a new object of class '<em>Implicit Variable</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Implicit Variable</em>'.
	 * @generated
	 */
	ImplicitVariable createImplicitVariable();

	/**
	 * Returns a new object of class '<em>Node</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Node</em>'.
	 * @generated
	 */
	Node createNode();

	/**
	 * Returns a new object of class '<em>Scope Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Scope Declaration</em>'.
	 * @generated
	 */
	ScopeDeclaration createScopeDeclaration();

	/**
	 * Returns a new object of class '<em>Type Scope</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Type Scope</em>'.
	 * @generated
	 */
	TypeScope createTypeScope();

	/**
	 * Returns a new object of class '<em>Range Multiplicity</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Range Multiplicity</em>'.
	 * @generated
	 */
	RangeMultiplicity createRangeMultiplicity();

	/**
	 * Returns a new object of class '<em>Exact Multiplicity</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Exact Multiplicity</em>'.
	 * @generated
	 */
	ExactMultiplicity createExactMultiplicity();

	/**
	 * Returns a new object of class '<em>Unbounded Multiplicity</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Unbounded Multiplicity</em>'.
	 * @generated
	 */
	UnboundedMultiplicity createUnboundedMultiplicity();

	/**
	 * Returns a new object of class '<em>Enum Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Enum Declaration</em>'.
	 * @generated
	 */
	EnumDeclaration createEnumDeclaration();

	/**
	 * Returns a new object of class '<em>Int Constant</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Int Constant</em>'.
	 * @generated
	 */
	IntConstant createIntConstant();

	/**
	 * Returns a new object of class '<em>Real Constant</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Real Constant</em>'.
	 * @generated
	 */
	RealConstant createRealConstant();

	/**
	 * Returns a new object of class '<em>String Constant</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>String Constant</em>'.
	 * @generated
	 */
	StringConstant createStringConstant();

	/**
	 * Returns a new object of class '<em>Node Assertion Argument</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Node Assertion Argument</em>'.
	 * @generated
	 */
	NodeAssertionArgument createNodeAssertionArgument();

	/**
	 * Returns a new object of class '<em>Node Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Node Declaration</em>'.
	 * @generated
	 */
	NodeDeclaration createNodeDeclaration();

	/**
	 * Returns a new object of class '<em>Wildcard Assertion Argument</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Wildcard Assertion Argument</em>'.
	 * @generated
	 */
	WildcardAssertionArgument createWildcardAssertionArgument();

	/**
	 * Returns a new object of class '<em>Rule Definition</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Rule Definition</em>'.
	 * @generated
	 */
	RuleDefinition createRuleDefinition();

	/**
	 * Returns a new object of class '<em>Consequent</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Consequent</em>'.
	 * @generated
	 */
	Consequent createConsequent();

	/**
	 * Returns a new object of class '<em>Assertion Action</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Assertion Action</em>'.
	 * @generated
	 */
	AssertionAction createAssertionAction();

	/**
	 * Returns a new object of class '<em>Variable Or Node Expr</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Variable Or Node Expr</em>'.
	 * @generated
	 */
	VariableOrNodeExpr createVariableOrNodeExpr();

	/**
	 * Returns a new object of class '<em>Arithmetic Unary Expr</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Arithmetic Unary Expr</em>'.
	 * @generated
	 */
	ArithmeticUnaryExpr createArithmeticUnaryExpr();

	/**
	 * Returns a new object of class '<em>Aggregation Expr</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Aggregation Expr</em>'.
	 * @generated
	 */
	AggregationExpr createAggregationExpr();

	/**
	 * Returns a new object of class '<em>Comparison Expr</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Comparison Expr</em>'.
	 * @generated
	 */
	ComparisonExpr createComparisonExpr();

	/**
	 * Returns a new object of class '<em>Negation Expr</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Negation Expr</em>'.
	 * @generated
	 */
	NegationExpr createNegationExpr();

	/**
	 * Returns a new object of class '<em>Function Definition</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Function Definition</em>'.
	 * @generated
	 */
	FunctionDefinition createFunctionDefinition();

	/**
	 * Returns a new object of class '<em>Conjunction</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Conjunction</em>'.
	 * @generated
	 */
	Conjunction createConjunction();

	/**
	 * Returns a new object of class '<em>Case</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Case</em>'.
	 * @generated
	 */
	Case createCase();

	/**
	 * Returns a new object of class '<em>Arithmetic Binary Expr</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Arithmetic Binary Expr</em>'.
	 * @generated
	 */
	ArithmeticBinaryExpr createArithmeticBinaryExpr();

	/**
	 * Returns a new object of class '<em>Range Expr</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Range Expr</em>'.
	 * @generated
	 */
	RangeExpr createRangeExpr();

	/**
	 * Returns a new object of class '<em>Logic Constant</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Logic Constant</em>'.
	 * @generated
	 */
	LogicConstant createLogicConstant();

	/**
	 * Returns a new object of class '<em>Import Statement</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Import Statement</em>'.
	 * @generated
	 */
	ImportStatement createImportStatement();

	/**
	 * Returns a new object of class '<em>Datatype Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Datatype Declaration</em>'.
	 * @generated
	 */
	DatatypeDeclaration createDatatypeDeclaration();

	/**
	 * Returns a new object of class '<em>Lattice Binary Expr</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Lattice Binary Expr</em>'.
	 * @generated
	 */
	LatticeBinaryExpr createLatticeBinaryExpr();

	/**
	 * Returns a new object of class '<em>Assignment Expr</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Assignment Expr</em>'.
	 * @generated
	 */
	AssignmentExpr createAssignmentExpr();

	/**
	 * Returns a new object of class '<em>Infinite Constant</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Infinite Constant</em>'.
	 * @generated
	 */
	InfiniteConstant createInfiniteConstant();

	/**
	 * Returns a new object of class '<em>Aggregator Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Aggregator Declaration</em>'.
	 * @generated
	 */
	AggregatorDeclaration createAggregatorDeclaration();

	/**
	 * Returns a new object of class '<em>Modal Expr</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Modal Expr</em>'.
	 * @generated
	 */
	ModalExpr createModalExpr();

	/**
	 * Returns a new object of class '<em>Assertion</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Assertion</em>'.
	 * @generated
	 */
	Assertion createAssertion();

	/**
	 * Returns a new object of class '<em>Annotation Container</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Annotation Container</em>'.
	 * @generated
	 */
	AnnotationContainer createAnnotationContainer();

	/**
	 * Returns a new object of class '<em>Annotation Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Annotation Declaration</em>'.
	 * @generated
	 */
	AnnotationDeclaration createAnnotationDeclaration();

	/**
	 * Returns a new object of class '<em>Annotation</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Annotation</em>'.
	 * @generated
	 */
	Annotation createAnnotation();

	/**
	 * Returns a new object of class '<em>Annotation Argument</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Annotation Argument</em>'.
	 * @generated
	 */
	AnnotationArgument createAnnotationArgument();

	/**
	 * Returns a new object of class '<em>Top Level Annotation</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Top Level Annotation</em>'.
	 * @generated
	 */
	TopLevelAnnotation createTopLevelAnnotation();

	/**
	 * Returns a new object of class '<em>Overloaded Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Overloaded Declaration</em>'.
	 * @generated
	 */
	OverloadedDeclaration createOverloadedDeclaration();

	/**
	 * Returns a new object of class '<em>Theory Action</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Theory Action</em>'.
	 * @generated
	 */
	TheoryAction createTheoryAction();

	/**
	 * Returns the package supported by this factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the package supported by this factory.
	 * @generated
	 */
	ProblemPackage getProblemPackage();

} //ProblemFactory
