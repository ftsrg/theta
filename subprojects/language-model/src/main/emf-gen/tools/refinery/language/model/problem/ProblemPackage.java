/**
 */
package tools.refinery.language.model.problem;

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EEnum;
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
 * @see tools.refinery.language.model.problem.ProblemFactory
 * @model kind="package"
 *        annotation="http://www.eclipse.org/emf/2002/Ecore settingDelegates='https://refinery.tools/emf/2024/ProblemDelegate'"
 * @generated
 */
public interface ProblemPackage extends EPackage
{
	/**
	 * The package name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNAME = "problem";

	/**
	 * The package namespace URI.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_URI = "https://refinery.tools/emf/2021/Problem";

	/**
	 * The package namespace name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_PREFIX = "problem";

	/**
	 * The singleton instance of the package.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	ProblemPackage eINSTANCE = tools.refinery.language.model.problem.impl.ProblemPackageImpl.init();

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.NamedElementImpl <em>Named Element</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.NamedElementImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getNamedElement()
	 * @generated
	 */
	int NAMED_ELEMENT = 3;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NAMED_ELEMENT__NAME = 0;

	/**
	 * The number of structural features of the '<em>Named Element</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NAMED_ELEMENT_FEATURE_COUNT = 1;

	/**
	 * The number of operations of the '<em>Named Element</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NAMED_ELEMENT_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.ProblemImpl <em>Problem</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.ProblemImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getProblem()
	 * @generated
	 */
	int PROBLEM = 0;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROBLEM__NAME = NAMED_ELEMENT__NAME;

	/**
	 * The feature id for the '<em><b>Nodes</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROBLEM__NODES = NAMED_ELEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Statements</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROBLEM__STATEMENTS = NAMED_ELEMENT_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Kind</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROBLEM__KIND = NAMED_ELEMENT_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Explicit Kind</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROBLEM__EXPLICIT_KIND = NAMED_ELEMENT_FEATURE_COUNT + 3;

	/**
	 * The number of structural features of the '<em>Problem</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROBLEM_FEATURE_COUNT = NAMED_ELEMENT_FEATURE_COUNT + 4;

	/**
	 * The number of operations of the '<em>Problem</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROBLEM_OPERATION_COUNT = NAMED_ELEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.Statement <em>Statement</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.Statement
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getStatement()
	 * @generated
	 */
	int STATEMENT = 13;

	/**
	 * The number of structural features of the '<em>Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATEMENT_FEATURE_COUNT = 0;

	/**
	 * The number of operations of the '<em>Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATEMENT_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.ClassDeclarationImpl <em>Class Declaration</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.ClassDeclarationImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getClassDeclaration()
	 * @generated
	 */
	int CLASS_DECLARATION = 1;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_DECLARATION__NAME = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Annotations</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_DECLARATION__ANNOTATIONS = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Abstract</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_DECLARATION__ABSTRACT = STATEMENT_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Feature Declarations</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_DECLARATION__FEATURE_DECLARATIONS = STATEMENT_FEATURE_COUNT + 3;

	/**
	 * The feature id for the '<em><b>New Node</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_DECLARATION__NEW_NODE = STATEMENT_FEATURE_COUNT + 4;

	/**
	 * The feature id for the '<em><b>Super Types</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_DECLARATION__SUPER_TYPES = STATEMENT_FEATURE_COUNT + 5;

	/**
	 * The number of structural features of the '<em>Class Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_DECLARATION_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 6;

	/**
	 * The number of operations of the '<em>Class Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_DECLARATION_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.RelationImpl <em>Relation</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.RelationImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getRelation()
	 * @generated
	 */
	int RELATION = 46;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RELATION__NAME = NAMED_ELEMENT__NAME;

	/**
	 * The number of structural features of the '<em>Relation</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RELATION_FEATURE_COUNT = NAMED_ELEMENT_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Relation</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RELATION_OPERATION_COUNT = NAMED_ELEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.ReferenceDeclarationImpl <em>Reference Declaration</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.ReferenceDeclarationImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getReferenceDeclaration()
	 * @generated
	 */
	int REFERENCE_DECLARATION = 2;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REFERENCE_DECLARATION__NAME = RELATION__NAME;

	/**
	 * The feature id for the '<em><b>Annotations</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REFERENCE_DECLARATION__ANNOTATIONS = RELATION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Opposite</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REFERENCE_DECLARATION__OPPOSITE = RELATION_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Multiplicity</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REFERENCE_DECLARATION__MULTIPLICITY = RELATION_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Kind</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REFERENCE_DECLARATION__KIND = RELATION_FEATURE_COUNT + 3;

	/**
	 * The feature id for the '<em><b>Reference Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REFERENCE_DECLARATION__REFERENCE_TYPE = RELATION_FEATURE_COUNT + 4;

	/**
	 * The feature id for the '<em><b>Invalid Multiplicity</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REFERENCE_DECLARATION__INVALID_MULTIPLICITY = RELATION_FEATURE_COUNT + 5;

	/**
	 * The feature id for the '<em><b>Super Sets</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REFERENCE_DECLARATION__SUPER_SETS = RELATION_FEATURE_COUNT + 6;

	/**
	 * The number of structural features of the '<em>Reference Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REFERENCE_DECLARATION_FEATURE_COUNT = RELATION_FEATURE_COUNT + 7;

	/**
	 * The number of operations of the '<em>Reference Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REFERENCE_DECLARATION_OPERATION_COUNT = RELATION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.ParametricDefinition <em>Parametric Definition</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.ParametricDefinition
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getParametricDefinition()
	 * @generated
	 */
	int PARAMETRIC_DEFINITION = 29;

	/**
	 * The feature id for the '<em><b>Annotations</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETRIC_DEFINITION__ANNOTATIONS = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Parameters</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETRIC_DEFINITION__PARAMETERS = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Parametric Definition</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETRIC_DEFINITION_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Parametric Definition</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETRIC_DEFINITION_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.PredicateDefinitionImpl <em>Predicate Definition</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.PredicateDefinitionImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getPredicateDefinition()
	 * @generated
	 */
	int PREDICATE_DEFINITION = 4;

	/**
	 * The feature id for the '<em><b>Annotations</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PREDICATE_DEFINITION__ANNOTATIONS = PARAMETRIC_DEFINITION__ANNOTATIONS;

	/**
	 * The feature id for the '<em><b>Parameters</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PREDICATE_DEFINITION__PARAMETERS = PARAMETRIC_DEFINITION__PARAMETERS;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PREDICATE_DEFINITION__NAME = PARAMETRIC_DEFINITION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Bodies</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PREDICATE_DEFINITION__BODIES = PARAMETRIC_DEFINITION_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Kind</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PREDICATE_DEFINITION__KIND = PARAMETRIC_DEFINITION_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Computed Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PREDICATE_DEFINITION__COMPUTED_VALUE = PARAMETRIC_DEFINITION_FEATURE_COUNT + 3;

	/**
	 * The feature id for the '<em><b>Super Sets</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PREDICATE_DEFINITION__SUPER_SETS = PARAMETRIC_DEFINITION_FEATURE_COUNT + 4;

	/**
	 * The number of structural features of the '<em>Predicate Definition</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PREDICATE_DEFINITION_FEATURE_COUNT = PARAMETRIC_DEFINITION_FEATURE_COUNT + 5;

	/**
	 * The number of operations of the '<em>Predicate Definition</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PREDICATE_DEFINITION_OPERATION_COUNT = PARAMETRIC_DEFINITION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.VariableOrNodeImpl <em>Variable Or Node</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.VariableOrNodeImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getVariableOrNode()
	 * @generated
	 */
	int VARIABLE_OR_NODE = 20;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_OR_NODE__NAME = NAMED_ELEMENT__NAME;

	/**
	 * The number of structural features of the '<em>Variable Or Node</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_OR_NODE_FEATURE_COUNT = NAMED_ELEMENT_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Variable Or Node</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_OR_NODE_OPERATION_COUNT = NAMED_ELEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.VariableImpl <em>Variable</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.VariableImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getVariable()
	 * @generated
	 */
	int VARIABLE = 6;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE__NAME = VARIABLE_OR_NODE__NAME;

	/**
	 * The number of structural features of the '<em>Variable</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_FEATURE_COUNT = VARIABLE_OR_NODE_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Variable</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_OPERATION_COUNT = VARIABLE_OR_NODE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.ParameterImpl <em>Parameter</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.ParameterImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getParameter()
	 * @generated
	 */
	int PARAMETER = 5;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER__NAME = VARIABLE__NAME;

	/**
	 * The feature id for the '<em><b>Annotations</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER__ANNOTATIONS = VARIABLE_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Parameter Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER__PARAMETER_TYPE = VARIABLE_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Kind</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER__KIND = VARIABLE_FEATURE_COUNT + 2;

	/**
	 * The number of structural features of the '<em>Parameter</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER_FEATURE_COUNT = VARIABLE_FEATURE_COUNT + 3;

	/**
	 * The number of operations of the '<em>Parameter</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER_OPERATION_COUNT = VARIABLE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.ExprImpl <em>Expr</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.ExprImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getExpr()
	 * @generated
	 */
	int EXPR = 34;

	/**
	 * The number of structural features of the '<em>Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPR_FEATURE_COUNT = 0;

	/**
	 * The number of operations of the '<em>Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPR_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.AtomImpl <em>Atom</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.AtomImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAtom()
	 * @generated
	 */
	int ATOM = 7;

	/**
	 * The feature id for the '<em><b>Transitive Closure</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ATOM__TRANSITIVE_CLOSURE = EXPR_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Arguments</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ATOM__ARGUMENTS = EXPR_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Relation</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ATOM__RELATION = EXPR_FEATURE_COUNT + 2;

	/**
	 * The number of structural features of the '<em>Atom</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ATOM_FEATURE_COUNT = EXPR_FEATURE_COUNT + 3;

	/**
	 * The number of operations of the '<em>Atom</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ATOM_OPERATION_COUNT = EXPR_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.ImplicitVariableImpl <em>Implicit Variable</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.ImplicitVariableImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getImplicitVariable()
	 * @generated
	 */
	int IMPLICIT_VARIABLE = 8;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IMPLICIT_VARIABLE__NAME = VARIABLE__NAME;

	/**
	 * The number of structural features of the '<em>Implicit Variable</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IMPLICIT_VARIABLE_FEATURE_COUNT = VARIABLE_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Implicit Variable</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IMPLICIT_VARIABLE_OPERATION_COUNT = VARIABLE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.ExistentialQuantifier <em>Existential Quantifier</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.ExistentialQuantifier
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getExistentialQuantifier()
	 * @generated
	 */
	int EXISTENTIAL_QUANTIFIER = 9;

	/**
	 * The feature id for the '<em><b>Implicit Variables</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXISTENTIAL_QUANTIFIER__IMPLICIT_VARIABLES = 0;

	/**
	 * The number of structural features of the '<em>Existential Quantifier</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXISTENTIAL_QUANTIFIER_FEATURE_COUNT = 1;

	/**
	 * The number of operations of the '<em>Existential Quantifier</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXISTENTIAL_QUANTIFIER_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.AbstractAssertionImpl <em>Abstract Assertion</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.AbstractAssertionImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAbstractAssertion()
	 * @generated
	 */
	int ABSTRACT_ASSERTION = 10;

	/**
	 * The feature id for the '<em><b>Implicit Variables</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ABSTRACT_ASSERTION__IMPLICIT_VARIABLES = EXISTENTIAL_QUANTIFIER__IMPLICIT_VARIABLES;

	/**
	 * The feature id for the '<em><b>Arguments</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ABSTRACT_ASSERTION__ARGUMENTS = EXISTENTIAL_QUANTIFIER_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Relation</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ABSTRACT_ASSERTION__RELATION = EXISTENTIAL_QUANTIFIER_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ABSTRACT_ASSERTION__VALUE = EXISTENTIAL_QUANTIFIER_FEATURE_COUNT + 2;

	/**
	 * The number of structural features of the '<em>Abstract Assertion</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ABSTRACT_ASSERTION_FEATURE_COUNT = EXISTENTIAL_QUANTIFIER_FEATURE_COUNT + 3;

	/**
	 * The number of operations of the '<em>Abstract Assertion</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ABSTRACT_ASSERTION_OPERATION_COUNT = EXISTENTIAL_QUANTIFIER_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.NodeImpl <em>Node</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.NodeImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getNode()
	 * @generated
	 */
	int NODE = 11;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NODE__NAME = VARIABLE_OR_NODE__NAME;

	/**
	 * The feature id for the '<em><b>Annotations</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NODE__ANNOTATIONS = VARIABLE_OR_NODE_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Node</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NODE_FEATURE_COUNT = VARIABLE_OR_NODE_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Node</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NODE_OPERATION_COUNT = VARIABLE_OR_NODE_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.ScopeDeclarationImpl <em>Scope Declaration</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.ScopeDeclarationImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getScopeDeclaration()
	 * @generated
	 */
	int SCOPE_DECLARATION = 12;

	/**
	 * The feature id for the '<em><b>Type Scopes</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SCOPE_DECLARATION__TYPE_SCOPES = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Scope Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SCOPE_DECLARATION_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Scope Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SCOPE_DECLARATION_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.TypeScopeImpl <em>Type Scope</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.TypeScopeImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getTypeScope()
	 * @generated
	 */
	int TYPE_SCOPE = 14;

	/**
	 * The feature id for the '<em><b>Increment</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_SCOPE__INCREMENT = 0;

	/**
	 * The feature id for the '<em><b>Multiplicity</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_SCOPE__MULTIPLICITY = 1;

	/**
	 * The feature id for the '<em><b>Target Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_SCOPE__TARGET_TYPE = 2;

	/**
	 * The number of structural features of the '<em>Type Scope</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_SCOPE_FEATURE_COUNT = 3;

	/**
	 * The number of operations of the '<em>Type Scope</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_SCOPE_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.MultiplicityImpl <em>Multiplicity</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.MultiplicityImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getMultiplicity()
	 * @generated
	 */
	int MULTIPLICITY = 15;

	/**
	 * The number of structural features of the '<em>Multiplicity</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTIPLICITY_FEATURE_COUNT = 0;

	/**
	 * The number of operations of the '<em>Multiplicity</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTIPLICITY_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.RangeMultiplicityImpl <em>Range Multiplicity</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.RangeMultiplicityImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getRangeMultiplicity()
	 * @generated
	 */
	int RANGE_MULTIPLICITY = 16;

	/**
	 * The feature id for the '<em><b>Lower Bound</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RANGE_MULTIPLICITY__LOWER_BOUND = MULTIPLICITY_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Upper Bound</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RANGE_MULTIPLICITY__UPPER_BOUND = MULTIPLICITY_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Range Multiplicity</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RANGE_MULTIPLICITY_FEATURE_COUNT = MULTIPLICITY_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Range Multiplicity</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RANGE_MULTIPLICITY_OPERATION_COUNT = MULTIPLICITY_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.ExactMultiplicityImpl <em>Exact Multiplicity</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.ExactMultiplicityImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getExactMultiplicity()
	 * @generated
	 */
	int EXACT_MULTIPLICITY = 17;

	/**
	 * The feature id for the '<em><b>Exact Value</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXACT_MULTIPLICITY__EXACT_VALUE = MULTIPLICITY_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Exact Multiplicity</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXACT_MULTIPLICITY_FEATURE_COUNT = MULTIPLICITY_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Exact Multiplicity</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXACT_MULTIPLICITY_OPERATION_COUNT = MULTIPLICITY_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.UnboundedMultiplicityImpl <em>Unbounded Multiplicity</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.UnboundedMultiplicityImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getUnboundedMultiplicity()
	 * @generated
	 */
	int UNBOUNDED_MULTIPLICITY = 18;

	/**
	 * The number of structural features of the '<em>Unbounded Multiplicity</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int UNBOUNDED_MULTIPLICITY_FEATURE_COUNT = MULTIPLICITY_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Unbounded Multiplicity</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int UNBOUNDED_MULTIPLICITY_OPERATION_COUNT = MULTIPLICITY_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.EnumDeclarationImpl <em>Enum Declaration</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.EnumDeclarationImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getEnumDeclaration()
	 * @generated
	 */
	int ENUM_DECLARATION = 19;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ENUM_DECLARATION__NAME = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Annotations</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ENUM_DECLARATION__ANNOTATIONS = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Literals</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ENUM_DECLARATION__LITERALS = STATEMENT_FEATURE_COUNT + 2;

	/**
	 * The number of structural features of the '<em>Enum Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ENUM_DECLARATION_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 3;

	/**
	 * The number of operations of the '<em>Enum Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ENUM_DECLARATION_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.ConstantImpl <em>Constant</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.ConstantImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getConstant()
	 * @generated
	 */
	int CONSTANT = 21;

	/**
	 * The number of structural features of the '<em>Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONSTANT_FEATURE_COUNT = EXPR_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONSTANT_OPERATION_COUNT = EXPR_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.IntConstantImpl <em>Int Constant</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.IntConstantImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getIntConstant()
	 * @generated
	 */
	int INT_CONSTANT = 22;

	/**
	 * The feature id for the '<em><b>Int Value</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INT_CONSTANT__INT_VALUE = CONSTANT_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Int Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INT_CONSTANT_FEATURE_COUNT = CONSTANT_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Int Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INT_CONSTANT_OPERATION_COUNT = CONSTANT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.RealConstantImpl <em>Real Constant</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.RealConstantImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getRealConstant()
	 * @generated
	 */
	int REAL_CONSTANT = 23;

	/**
	 * The feature id for the '<em><b>Real Value</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REAL_CONSTANT__REAL_VALUE = CONSTANT_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Real Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REAL_CONSTANT_FEATURE_COUNT = CONSTANT_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Real Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int REAL_CONSTANT_OPERATION_COUNT = CONSTANT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.StringConstantImpl <em>String Constant</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.StringConstantImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getStringConstant()
	 * @generated
	 */
	int STRING_CONSTANT = 24;

	/**
	 * The feature id for the '<em><b>String Value</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_CONSTANT__STRING_VALUE = CONSTANT_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>String Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_CONSTANT_FEATURE_COUNT = CONSTANT_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>String Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_CONSTANT_OPERATION_COUNT = CONSTANT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.AssertionArgumentImpl <em>Assertion Argument</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.AssertionArgumentImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAssertionArgument()
	 * @generated
	 */
	int ASSERTION_ARGUMENT = 26;

	/**
	 * The number of structural features of the '<em>Assertion Argument</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION_ARGUMENT_FEATURE_COUNT = 0;

	/**
	 * The number of operations of the '<em>Assertion Argument</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION_ARGUMENT_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.NodeAssertionArgumentImpl <em>Node Assertion Argument</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.NodeAssertionArgumentImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getNodeAssertionArgument()
	 * @generated
	 */
	int NODE_ASSERTION_ARGUMENT = 25;

	/**
	 * The feature id for the '<em><b>Node</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NODE_ASSERTION_ARGUMENT__NODE = ASSERTION_ARGUMENT_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Node Assertion Argument</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NODE_ASSERTION_ARGUMENT_FEATURE_COUNT = ASSERTION_ARGUMENT_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Node Assertion Argument</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NODE_ASSERTION_ARGUMENT_OPERATION_COUNT = ASSERTION_ARGUMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.NodeDeclarationImpl <em>Node Declaration</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.NodeDeclarationImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getNodeDeclaration()
	 * @generated
	 */
	int NODE_DECLARATION = 27;

	/**
	 * The feature id for the '<em><b>Annotations</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NODE_DECLARATION__ANNOTATIONS = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Nodes</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NODE_DECLARATION__NODES = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Kind</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NODE_DECLARATION__KIND = STATEMENT_FEATURE_COUNT + 2;

	/**
	 * The number of structural features of the '<em>Node Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NODE_DECLARATION_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 3;

	/**
	 * The number of operations of the '<em>Node Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NODE_DECLARATION_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.WildcardAssertionArgumentImpl <em>Wildcard Assertion Argument</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.WildcardAssertionArgumentImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getWildcardAssertionArgument()
	 * @generated
	 */
	int WILDCARD_ASSERTION_ARGUMENT = 28;

	/**
	 * The number of structural features of the '<em>Wildcard Assertion Argument</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int WILDCARD_ASSERTION_ARGUMENT_FEATURE_COUNT = ASSERTION_ARGUMENT_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Wildcard Assertion Argument</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int WILDCARD_ASSERTION_ARGUMENT_OPERATION_COUNT = ASSERTION_ARGUMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.RuleDefinitionImpl <em>Rule Definition</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.RuleDefinitionImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getRuleDefinition()
	 * @generated
	 */
	int RULE_DEFINITION = 30;

	/**
	 * The feature id for the '<em><b>Annotations</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RULE_DEFINITION__ANNOTATIONS = PARAMETRIC_DEFINITION__ANNOTATIONS;

	/**
	 * The feature id for the '<em><b>Parameters</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RULE_DEFINITION__PARAMETERS = PARAMETRIC_DEFINITION__PARAMETERS;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RULE_DEFINITION__NAME = PARAMETRIC_DEFINITION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Consequents</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RULE_DEFINITION__CONSEQUENTS = PARAMETRIC_DEFINITION_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Preconditions</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RULE_DEFINITION__PRECONDITIONS = PARAMETRIC_DEFINITION_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Kind</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RULE_DEFINITION__KIND = PARAMETRIC_DEFINITION_FEATURE_COUNT + 3;

	/**
	 * The number of structural features of the '<em>Rule Definition</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RULE_DEFINITION_FEATURE_COUNT = PARAMETRIC_DEFINITION_FEATURE_COUNT + 4;

	/**
	 * The number of operations of the '<em>Rule Definition</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RULE_DEFINITION_OPERATION_COUNT = PARAMETRIC_DEFINITION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.ConsequentImpl <em>Consequent</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.ConsequentImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getConsequent()
	 * @generated
	 */
	int CONSEQUENT = 31;

	/**
	 * The feature id for the '<em><b>Actions</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONSEQUENT__ACTIONS = 0;

	/**
	 * The number of structural features of the '<em>Consequent</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONSEQUENT_FEATURE_COUNT = 1;

	/**
	 * The number of operations of the '<em>Consequent</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONSEQUENT_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.Action <em>Action</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.Action
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAction()
	 * @generated
	 */
	int ACTION = 32;

	/**
	 * The number of structural features of the '<em>Action</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ACTION_FEATURE_COUNT = 0;

	/**
	 * The number of operations of the '<em>Action</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ACTION_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.AssertionActionImpl <em>Assertion Action</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.AssertionActionImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAssertionAction()
	 * @generated
	 */
	int ASSERTION_ACTION = 33;

	/**
	 * The feature id for the '<em><b>Implicit Variables</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION_ACTION__IMPLICIT_VARIABLES = ACTION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Arguments</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION_ACTION__ARGUMENTS = ACTION_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Relation</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION_ACTION__RELATION = ACTION_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION_ACTION__VALUE = ACTION_FEATURE_COUNT + 3;

	/**
	 * The number of structural features of the '<em>Assertion Action</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION_ACTION_FEATURE_COUNT = ACTION_FEATURE_COUNT + 4;

	/**
	 * The number of operations of the '<em>Assertion Action</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION_ACTION_OPERATION_COUNT = ACTION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.VariableOrNodeExprImpl <em>Variable Or Node Expr</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.VariableOrNodeExprImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getVariableOrNodeExpr()
	 * @generated
	 */
	int VARIABLE_OR_NODE_EXPR = 35;

	/**
	 * The feature id for the '<em><b>Variable Or Node</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_OR_NODE_EXPR__VARIABLE_OR_NODE = EXPR_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Singleton Variable</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_OR_NODE_EXPR__SINGLETON_VARIABLE = EXPR_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Relation</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_OR_NODE_EXPR__RELATION = EXPR_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Element</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_OR_NODE_EXPR__ELEMENT = EXPR_FEATURE_COUNT + 3;

	/**
	 * The number of structural features of the '<em>Variable Or Node Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_OR_NODE_EXPR_FEATURE_COUNT = EXPR_FEATURE_COUNT + 4;

	/**
	 * The number of operations of the '<em>Variable Or Node Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_OR_NODE_EXPR_OPERATION_COUNT = EXPR_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.BinaryExprImpl <em>Binary Expr</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.BinaryExprImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getBinaryExpr()
	 * @generated
	 */
	int BINARY_EXPR = 36;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BINARY_EXPR__LEFT = EXPR_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BINARY_EXPR__RIGHT = EXPR_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Binary Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BINARY_EXPR_FEATURE_COUNT = EXPR_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Binary Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BINARY_EXPR_OPERATION_COUNT = EXPR_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.UnaryExprImpl <em>Unary Expr</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.UnaryExprImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getUnaryExpr()
	 * @generated
	 */
	int UNARY_EXPR = 37;

	/**
	 * The feature id for the '<em><b>Body</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int UNARY_EXPR__BODY = EXPR_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Unary Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int UNARY_EXPR_FEATURE_COUNT = EXPR_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Unary Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int UNARY_EXPR_OPERATION_COUNT = EXPR_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.ArithmeticUnaryExprImpl <em>Arithmetic Unary Expr</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.ArithmeticUnaryExprImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getArithmeticUnaryExpr()
	 * @generated
	 */
	int ARITHMETIC_UNARY_EXPR = 38;

	/**
	 * The feature id for the '<em><b>Body</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARITHMETIC_UNARY_EXPR__BODY = UNARY_EXPR__BODY;

	/**
	 * The feature id for the '<em><b>Op</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARITHMETIC_UNARY_EXPR__OP = UNARY_EXPR_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Arithmetic Unary Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARITHMETIC_UNARY_EXPR_FEATURE_COUNT = UNARY_EXPR_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Arithmetic Unary Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARITHMETIC_UNARY_EXPR_OPERATION_COUNT = UNARY_EXPR_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.AggregationExprImpl <em>Aggregation Expr</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.AggregationExprImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAggregationExpr()
	 * @generated
	 */
	int AGGREGATION_EXPR = 39;

	/**
	 * The feature id for the '<em><b>Implicit Variables</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATION_EXPR__IMPLICIT_VARIABLES = EXPR_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATION_EXPR__VALUE = EXPR_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Condition</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATION_EXPR__CONDITION = EXPR_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Aggregator</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATION_EXPR__AGGREGATOR = EXPR_FEATURE_COUNT + 3;

	/**
	 * The number of structural features of the '<em>Aggregation Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATION_EXPR_FEATURE_COUNT = EXPR_FEATURE_COUNT + 4;

	/**
	 * The number of operations of the '<em>Aggregation Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATION_EXPR_OPERATION_COUNT = EXPR_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.ComparisonExprImpl <em>Comparison Expr</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.ComparisonExprImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getComparisonExpr()
	 * @generated
	 */
	int COMPARISON_EXPR = 40;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMPARISON_EXPR__LEFT = BINARY_EXPR__LEFT;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMPARISON_EXPR__RIGHT = BINARY_EXPR__RIGHT;

	/**
	 * The feature id for the '<em><b>Op</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMPARISON_EXPR__OP = BINARY_EXPR_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Comparison Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMPARISON_EXPR_FEATURE_COUNT = BINARY_EXPR_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Comparison Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMPARISON_EXPR_OPERATION_COUNT = BINARY_EXPR_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.NegationExprImpl <em>Negation Expr</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.NegationExprImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getNegationExpr()
	 * @generated
	 */
	int NEGATION_EXPR = 41;

	/**
	 * The feature id for the '<em><b>Implicit Variables</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEGATION_EXPR__IMPLICIT_VARIABLES = EXISTENTIAL_QUANTIFIER__IMPLICIT_VARIABLES;

	/**
	 * The feature id for the '<em><b>Body</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEGATION_EXPR__BODY = EXISTENTIAL_QUANTIFIER_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Negation Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEGATION_EXPR_FEATURE_COUNT = EXISTENTIAL_QUANTIFIER_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Negation Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEGATION_EXPR_OPERATION_COUNT = EXISTENTIAL_QUANTIFIER_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.FunctionDefinitionImpl <em>Function Definition</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.FunctionDefinitionImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getFunctionDefinition()
	 * @generated
	 */
	int FUNCTION_DEFINITION = 42;

	/**
	 * The feature id for the '<em><b>Annotations</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FUNCTION_DEFINITION__ANNOTATIONS = PARAMETRIC_DEFINITION__ANNOTATIONS;

	/**
	 * The feature id for the '<em><b>Parameters</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FUNCTION_DEFINITION__PARAMETERS = PARAMETRIC_DEFINITION__PARAMETERS;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FUNCTION_DEFINITION__NAME = PARAMETRIC_DEFINITION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Cases</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FUNCTION_DEFINITION__CASES = PARAMETRIC_DEFINITION_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Function Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FUNCTION_DEFINITION__FUNCTION_TYPE = PARAMETRIC_DEFINITION_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Shadow</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FUNCTION_DEFINITION__SHADOW = PARAMETRIC_DEFINITION_FEATURE_COUNT + 3;

	/**
	 * The feature id for the '<em><b>Computed Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FUNCTION_DEFINITION__COMPUTED_VALUE = PARAMETRIC_DEFINITION_FEATURE_COUNT + 4;

	/**
	 * The feature id for the '<em><b>Domain Predicate</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FUNCTION_DEFINITION__DOMAIN_PREDICATE = PARAMETRIC_DEFINITION_FEATURE_COUNT + 5;

	/**
	 * The number of structural features of the '<em>Function Definition</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FUNCTION_DEFINITION_FEATURE_COUNT = PARAMETRIC_DEFINITION_FEATURE_COUNT + 6;

	/**
	 * The number of operations of the '<em>Function Definition</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FUNCTION_DEFINITION_OPERATION_COUNT = PARAMETRIC_DEFINITION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.ConjunctionImpl <em>Conjunction</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.ConjunctionImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getConjunction()
	 * @generated
	 */
	int CONJUNCTION = 43;

	/**
	 * The feature id for the '<em><b>Implicit Variables</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONJUNCTION__IMPLICIT_VARIABLES = EXISTENTIAL_QUANTIFIER__IMPLICIT_VARIABLES;

	/**
	 * The feature id for the '<em><b>Literals</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONJUNCTION__LITERALS = EXISTENTIAL_QUANTIFIER_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Conjunction</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONJUNCTION_FEATURE_COUNT = EXISTENTIAL_QUANTIFIER_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Conjunction</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CONJUNCTION_OPERATION_COUNT = EXISTENTIAL_QUANTIFIER_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.CaseImpl <em>Case</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.CaseImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getCase()
	 * @generated
	 */
	int CASE = 44;

	/**
	 * The feature id for the '<em><b>Condition</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CASE__CONDITION = 0;

	/**
	 * The feature id for the '<em><b>Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CASE__VALUE = 1;

	/**
	 * The number of structural features of the '<em>Case</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CASE_FEATURE_COUNT = 2;

	/**
	 * The number of operations of the '<em>Case</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CASE_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.ArithmeticBinaryExprImpl <em>Arithmetic Binary Expr</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.ArithmeticBinaryExprImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getArithmeticBinaryExpr()
	 * @generated
	 */
	int ARITHMETIC_BINARY_EXPR = 45;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARITHMETIC_BINARY_EXPR__LEFT = BINARY_EXPR__LEFT;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARITHMETIC_BINARY_EXPR__RIGHT = BINARY_EXPR__RIGHT;

	/**
	 * The feature id for the '<em><b>Op</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARITHMETIC_BINARY_EXPR__OP = BINARY_EXPR_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Arithmetic Binary Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARITHMETIC_BINARY_EXPR_FEATURE_COUNT = BINARY_EXPR_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Arithmetic Binary Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARITHMETIC_BINARY_EXPR_OPERATION_COUNT = BINARY_EXPR_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.RangeExprImpl <em>Range Expr</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.RangeExprImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getRangeExpr()
	 * @generated
	 */
	int RANGE_EXPR = 47;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RANGE_EXPR__LEFT = BINARY_EXPR__LEFT;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RANGE_EXPR__RIGHT = BINARY_EXPR__RIGHT;

	/**
	 * The number of structural features of the '<em>Range Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RANGE_EXPR_FEATURE_COUNT = BINARY_EXPR_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Range Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RANGE_EXPR_OPERATION_COUNT = BINARY_EXPR_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.LogicConstantImpl <em>Logic Constant</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.LogicConstantImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getLogicConstant()
	 * @generated
	 */
	int LOGIC_CONSTANT = 48;

	/**
	 * The feature id for the '<em><b>Logic Value</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int LOGIC_CONSTANT__LOGIC_VALUE = CONSTANT_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Logic Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int LOGIC_CONSTANT_FEATURE_COUNT = CONSTANT_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Logic Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int LOGIC_CONSTANT_OPERATION_COUNT = CONSTANT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.ImportStatementImpl <em>Import Statement</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.ImportStatementImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getImportStatement()
	 * @generated
	 */
	int IMPORT_STATEMENT = 49;

	/**
	 * The feature id for the '<em><b>Imported Module</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IMPORT_STATEMENT__IMPORTED_MODULE = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Alias</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IMPORT_STATEMENT__ALIAS = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Import Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IMPORT_STATEMENT_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Import Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IMPORT_STATEMENT_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.DatatypeDeclarationImpl <em>Datatype Declaration</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.DatatypeDeclarationImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getDatatypeDeclaration()
	 * @generated
	 */
	int DATATYPE_DECLARATION = 50;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DATATYPE_DECLARATION__NAME = RELATION__NAME;

	/**
	 * The feature id for the '<em><b>Annotations</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DATATYPE_DECLARATION__ANNOTATIONS = RELATION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Datatype Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DATATYPE_DECLARATION_FEATURE_COUNT = RELATION_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Datatype Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DATATYPE_DECLARATION_OPERATION_COUNT = RELATION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.LatticeBinaryExprImpl <em>Lattice Binary Expr</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.LatticeBinaryExprImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getLatticeBinaryExpr()
	 * @generated
	 */
	int LATTICE_BINARY_EXPR = 51;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int LATTICE_BINARY_EXPR__LEFT = BINARY_EXPR__LEFT;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int LATTICE_BINARY_EXPR__RIGHT = BINARY_EXPR__RIGHT;

	/**
	 * The feature id for the '<em><b>Op</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int LATTICE_BINARY_EXPR__OP = BINARY_EXPR_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Lattice Binary Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int LATTICE_BINARY_EXPR_FEATURE_COUNT = BINARY_EXPR_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Lattice Binary Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int LATTICE_BINARY_EXPR_OPERATION_COUNT = BINARY_EXPR_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.AssignmentExprImpl <em>Assignment Expr</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.AssignmentExprImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAssignmentExpr()
	 * @generated
	 */
	int ASSIGNMENT_EXPR = 52;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSIGNMENT_EXPR__LEFT = BINARY_EXPR__LEFT;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSIGNMENT_EXPR__RIGHT = BINARY_EXPR__RIGHT;

	/**
	 * The number of structural features of the '<em>Assignment Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSIGNMENT_EXPR_FEATURE_COUNT = BINARY_EXPR_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Assignment Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSIGNMENT_EXPR_OPERATION_COUNT = BINARY_EXPR_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.InfiniteConstantImpl <em>Infinite Constant</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.InfiniteConstantImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getInfiniteConstant()
	 * @generated
	 */
	int INFINITE_CONSTANT = 53;

	/**
	 * The number of structural features of the '<em>Infinite Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFINITE_CONSTANT_FEATURE_COUNT = CONSTANT_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Infinite Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFINITE_CONSTANT_OPERATION_COUNT = CONSTANT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.AggregatorDeclarationImpl <em>Aggregator Declaration</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.AggregatorDeclarationImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAggregatorDeclaration()
	 * @generated
	 */
	int AGGREGATOR_DECLARATION = 54;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATOR_DECLARATION__NAME = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Annotations</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATOR_DECLARATION__ANNOTATIONS = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Aggregator Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATOR_DECLARATION_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Aggregator Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATOR_DECLARATION_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.ModalExprImpl <em>Modal Expr</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.ModalExprImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getModalExpr()
	 * @generated
	 */
	int MODAL_EXPR = 55;

	/**
	 * The feature id for the '<em><b>Body</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MODAL_EXPR__BODY = UNARY_EXPR__BODY;

	/**
	 * The feature id for the '<em><b>Concreteness</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MODAL_EXPR__CONCRETENESS = UNARY_EXPR_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Modality</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MODAL_EXPR__MODALITY = UNARY_EXPR_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Modal Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MODAL_EXPR_FEATURE_COUNT = UNARY_EXPR_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Modal Expr</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MODAL_EXPR_OPERATION_COUNT = UNARY_EXPR_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.AssertionImpl <em>Assertion</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.AssertionImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAssertion()
	 * @generated
	 */
	int ASSERTION = 56;

	/**
	 * The feature id for the '<em><b>Implicit Variables</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION__IMPLICIT_VARIABLES = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Arguments</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION__ARGUMENTS = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Relation</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION__RELATION = STATEMENT_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION__VALUE = STATEMENT_FEATURE_COUNT + 3;

	/**
	 * The feature id for the '<em><b>Default</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION__DEFAULT = STATEMENT_FEATURE_COUNT + 4;

	/**
	 * The number of structural features of the '<em>Assertion</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 5;

	/**
	 * The number of operations of the '<em>Assertion</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.AnnotatedElement <em>Annotated Element</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.AnnotatedElement
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAnnotatedElement()
	 * @generated
	 */
	int ANNOTATED_ELEMENT = 57;

	/**
	 * The feature id for the '<em><b>Annotations</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATED_ELEMENT__ANNOTATIONS = 0;

	/**
	 * The number of structural features of the '<em>Annotated Element</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATED_ELEMENT_FEATURE_COUNT = 1;

	/**
	 * The number of operations of the '<em>Annotated Element</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATED_ELEMENT_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.AnnotationContainerImpl <em>Annotation Container</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.AnnotationContainerImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAnnotationContainer()
	 * @generated
	 */
	int ANNOTATION_CONTAINER = 58;

	/**
	 * The feature id for the '<em><b>Annotations</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATION_CONTAINER__ANNOTATIONS = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Annotation Container</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATION_CONTAINER_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Annotation Container</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATION_CONTAINER_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.AnnotationDeclarationImpl <em>Annotation Declaration</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.AnnotationDeclarationImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAnnotationDeclaration()
	 * @generated
	 */
	int ANNOTATION_DECLARATION = 59;

	/**
	 * The feature id for the '<em><b>Annotations</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATION_DECLARATION__ANNOTATIONS = PARAMETRIC_DEFINITION__ANNOTATIONS;

	/**
	 * The feature id for the '<em><b>Parameters</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATION_DECLARATION__PARAMETERS = PARAMETRIC_DEFINITION__PARAMETERS;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATION_DECLARATION__NAME = PARAMETRIC_DEFINITION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Annotation Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATION_DECLARATION_FEATURE_COUNT = PARAMETRIC_DEFINITION_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Annotation Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATION_DECLARATION_OPERATION_COUNT = PARAMETRIC_DEFINITION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.AnnotationImpl <em>Annotation</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.AnnotationImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAnnotation()
	 * @generated
	 */
	int ANNOTATION = 60;

	/**
	 * The feature id for the '<em><b>Declaration</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATION__DECLARATION = 0;

	/**
	 * The feature id for the '<em><b>Arguments</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATION__ARGUMENTS = 1;

	/**
	 * The number of structural features of the '<em>Annotation</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATION_FEATURE_COUNT = 2;

	/**
	 * The number of operations of the '<em>Annotation</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATION_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.AnnotationArgumentImpl <em>Annotation Argument</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.AnnotationArgumentImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAnnotationArgument()
	 * @generated
	 */
	int ANNOTATION_ARGUMENT = 61;

	/**
	 * The feature id for the '<em><b>Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATION_ARGUMENT__VALUE = 0;

	/**
	 * The feature id for the '<em><b>Parameter</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATION_ARGUMENT__PARAMETER = 1;

	/**
	 * The number of structural features of the '<em>Annotation Argument</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATION_ARGUMENT_FEATURE_COUNT = 2;

	/**
	 * The number of operations of the '<em>Annotation Argument</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ANNOTATION_ARGUMENT_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.TopLevelAnnotationImpl <em>Top Level Annotation</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.TopLevelAnnotationImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getTopLevelAnnotation()
	 * @generated
	 */
	int TOP_LEVEL_ANNOTATION = 62;

	/**
	 * The feature id for the '<em><b>Annotation</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TOP_LEVEL_ANNOTATION__ANNOTATION = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Top Level Annotation</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TOP_LEVEL_ANNOTATION_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Top Level Annotation</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TOP_LEVEL_ANNOTATION_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.OverloadedDeclarationImpl <em>Overloaded Declaration</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.OverloadedDeclarationImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getOverloadedDeclaration()
	 * @generated
	 */
	int OVERLOADED_DECLARATION = 63;

	/**
	 * The feature id for the '<em><b>Annotations</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OVERLOADED_DECLARATION__ANNOTATIONS = PARAMETRIC_DEFINITION__ANNOTATIONS;

	/**
	 * The feature id for the '<em><b>Parameters</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OVERLOADED_DECLARATION__PARAMETERS = PARAMETRIC_DEFINITION__PARAMETERS;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OVERLOADED_DECLARATION__NAME = PARAMETRIC_DEFINITION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Shadow</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OVERLOADED_DECLARATION__SHADOW = PARAMETRIC_DEFINITION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Overloaded Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OVERLOADED_DECLARATION_FEATURE_COUNT = PARAMETRIC_DEFINITION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Overloaded Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OVERLOADED_DECLARATION_OPERATION_COUNT = PARAMETRIC_DEFINITION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.impl.TheoryActionImpl <em>Theory Action</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.impl.TheoryActionImpl
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getTheoryAction()
	 * @generated
	 */
	int THEORY_ACTION = 64;

	/**
	 * The feature id for the '<em><b>Implicit Variables</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int THEORY_ACTION__IMPLICIT_VARIABLES = ACTION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Term</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int THEORY_ACTION__TERM = ACTION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Theory Action</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int THEORY_ACTION_FEATURE_COUNT = ACTION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Theory Action</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int THEORY_ACTION_OPERATION_COUNT = ACTION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.LogicValue <em>Logic Value</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.LogicValue
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getLogicValue()
	 * @generated
	 */
	int LOGIC_VALUE = 65;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.ComparisonOp <em>Comparison Op</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.ComparisonOp
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getComparisonOp()
	 * @generated
	 */
	int COMPARISON_OP = 66;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.ReferenceKind <em>Reference Kind</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.ReferenceKind
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getReferenceKind()
	 * @generated
	 */
	int REFERENCE_KIND = 67;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.UnaryOp <em>Unary Op</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.UnaryOp
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getUnaryOp()
	 * @generated
	 */
	int UNARY_OP = 68;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.BinaryOp <em>Binary Op</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.BinaryOp
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getBinaryOp()
	 * @generated
	 */
	int BINARY_OP = 69;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.ModuleKind <em>Module Kind</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.ModuleKind
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getModuleKind()
	 * @generated
	 */
	int MODULE_KIND = 70;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.NodeKind <em>Node Kind</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.NodeKind
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getNodeKind()
	 * @generated
	 */
	int NODE_KIND = 71;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.LatticeBinaryOp <em>Lattice Binary Op</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.LatticeBinaryOp
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getLatticeBinaryOp()
	 * @generated
	 */
	int LATTICE_BINARY_OP = 72;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.Modality <em>Modality</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.Modality
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getModality()
	 * @generated
	 */
	int MODALITY = 73;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.Concreteness <em>Concreteness</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.Concreteness
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getConcreteness()
	 * @generated
	 */
	int CONCRETENESS = 74;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.RuleKind <em>Rule Kind</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.RuleKind
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getRuleKind()
	 * @generated
	 */
	int RULE_KIND = 75;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.PredicateKind <em>Predicate Kind</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.PredicateKind
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getPredicateKind()
	 * @generated
	 */
	int PREDICATE_KIND = 76;

	/**
	 * The meta object id for the '{@link tools.refinery.language.model.problem.ParameterKind <em>Parameter Kind</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see tools.refinery.language.model.problem.ParameterKind
	 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getParameterKind()
	 * @generated
	 */
	int PARAMETER_KIND = 77;


	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.Problem <em>Problem</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Problem</em>'.
	 * @see tools.refinery.language.model.problem.Problem
	 * @generated
	 */
	EClass getProblem();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.Problem#getNodes <em>Nodes</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Nodes</em>'.
	 * @see tools.refinery.language.model.problem.Problem#getNodes()
	 * @see #getProblem()
	 * @generated
	 */
	EReference getProblem_Nodes();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.Problem#getStatements <em>Statements</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Statements</em>'.
	 * @see tools.refinery.language.model.problem.Problem#getStatements()
	 * @see #getProblem()
	 * @generated
	 */
	EReference getProblem_Statements();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.Problem#getKind <em>Kind</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Kind</em>'.
	 * @see tools.refinery.language.model.problem.Problem#getKind()
	 * @see #getProblem()
	 * @generated
	 */
	EAttribute getProblem_Kind();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.Problem#isExplicitKind <em>Explicit Kind</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Explicit Kind</em>'.
	 * @see tools.refinery.language.model.problem.Problem#isExplicitKind()
	 * @see #getProblem()
	 * @generated
	 */
	EAttribute getProblem_ExplicitKind();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.ClassDeclaration <em>Class Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Class Declaration</em>'.
	 * @see tools.refinery.language.model.problem.ClassDeclaration
	 * @generated
	 */
	EClass getClassDeclaration();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.ClassDeclaration#isAbstract <em>Abstract</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Abstract</em>'.
	 * @see tools.refinery.language.model.problem.ClassDeclaration#isAbstract()
	 * @see #getClassDeclaration()
	 * @generated
	 */
	EAttribute getClassDeclaration_Abstract();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.ClassDeclaration#getFeatureDeclarations <em>Feature Declarations</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Feature Declarations</em>'.
	 * @see tools.refinery.language.model.problem.ClassDeclaration#getFeatureDeclarations()
	 * @see #getClassDeclaration()
	 * @generated
	 */
	EReference getClassDeclaration_FeatureDeclarations();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.ClassDeclaration#getNewNode <em>New Node</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>New Node</em>'.
	 * @see tools.refinery.language.model.problem.ClassDeclaration#getNewNode()
	 * @see #getClassDeclaration()
	 * @generated
	 */
	EReference getClassDeclaration_NewNode();

	/**
	 * Returns the meta object for the reference list '{@link tools.refinery.language.model.problem.ClassDeclaration#getSuperTypes <em>Super Types</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Super Types</em>'.
	 * @see tools.refinery.language.model.problem.ClassDeclaration#getSuperTypes()
	 * @see #getClassDeclaration()
	 * @generated
	 */
	EReference getClassDeclaration_SuperTypes();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.ReferenceDeclaration <em>Reference Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Reference Declaration</em>'.
	 * @see tools.refinery.language.model.problem.ReferenceDeclaration
	 * @generated
	 */
	EClass getReferenceDeclaration();

	/**
	 * Returns the meta object for the reference '{@link tools.refinery.language.model.problem.ReferenceDeclaration#getOpposite <em>Opposite</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Opposite</em>'.
	 * @see tools.refinery.language.model.problem.ReferenceDeclaration#getOpposite()
	 * @see #getReferenceDeclaration()
	 * @generated
	 */
	EReference getReferenceDeclaration_Opposite();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.ReferenceDeclaration#getMultiplicity <em>Multiplicity</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Multiplicity</em>'.
	 * @see tools.refinery.language.model.problem.ReferenceDeclaration#getMultiplicity()
	 * @see #getReferenceDeclaration()
	 * @generated
	 */
	EReference getReferenceDeclaration_Multiplicity();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.ReferenceDeclaration#getKind <em>Kind</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Kind</em>'.
	 * @see tools.refinery.language.model.problem.ReferenceDeclaration#getKind()
	 * @see #getReferenceDeclaration()
	 * @generated
	 */
	EAttribute getReferenceDeclaration_Kind();

	/**
	 * Returns the meta object for the reference '{@link tools.refinery.language.model.problem.ReferenceDeclaration#getReferenceType <em>Reference Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Reference Type</em>'.
	 * @see tools.refinery.language.model.problem.ReferenceDeclaration#getReferenceType()
	 * @see #getReferenceDeclaration()
	 * @generated
	 */
	EReference getReferenceDeclaration_ReferenceType();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.ReferenceDeclaration#getInvalidMultiplicity <em>Invalid Multiplicity</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Invalid Multiplicity</em>'.
	 * @see tools.refinery.language.model.problem.ReferenceDeclaration#getInvalidMultiplicity()
	 * @see #getReferenceDeclaration()
	 * @generated
	 */
	EReference getReferenceDeclaration_InvalidMultiplicity();

	/**
	 * Returns the meta object for the reference list '{@link tools.refinery.language.model.problem.ReferenceDeclaration#getSuperSets <em>Super Sets</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Super Sets</em>'.
	 * @see tools.refinery.language.model.problem.ReferenceDeclaration#getSuperSets()
	 * @see #getReferenceDeclaration()
	 * @generated
	 */
	EReference getReferenceDeclaration_SuperSets();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.NamedElement <em>Named Element</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Named Element</em>'.
	 * @see tools.refinery.language.model.problem.NamedElement
	 * @generated
	 */
	EClass getNamedElement();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.NamedElement#getName <em>Name</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Name</em>'.
	 * @see tools.refinery.language.model.problem.NamedElement#getName()
	 * @see #getNamedElement()
	 * @generated
	 */
	EAttribute getNamedElement_Name();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.PredicateDefinition <em>Predicate Definition</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Predicate Definition</em>'.
	 * @see tools.refinery.language.model.problem.PredicateDefinition
	 * @generated
	 */
	EClass getPredicateDefinition();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.PredicateDefinition#getBodies <em>Bodies</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Bodies</em>'.
	 * @see tools.refinery.language.model.problem.PredicateDefinition#getBodies()
	 * @see #getPredicateDefinition()
	 * @generated
	 */
	EReference getPredicateDefinition_Bodies();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.PredicateDefinition#getKind <em>Kind</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Kind</em>'.
	 * @see tools.refinery.language.model.problem.PredicateDefinition#getKind()
	 * @see #getPredicateDefinition()
	 * @generated
	 */
	EAttribute getPredicateDefinition_Kind();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.PredicateDefinition#getComputedValue <em>Computed Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Computed Value</em>'.
	 * @see tools.refinery.language.model.problem.PredicateDefinition#getComputedValue()
	 * @see #getPredicateDefinition()
	 * @generated
	 */
	EReference getPredicateDefinition_ComputedValue();

	/**
	 * Returns the meta object for the reference list '{@link tools.refinery.language.model.problem.PredicateDefinition#getSuperSets <em>Super Sets</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Super Sets</em>'.
	 * @see tools.refinery.language.model.problem.PredicateDefinition#getSuperSets()
	 * @see #getPredicateDefinition()
	 * @generated
	 */
	EReference getPredicateDefinition_SuperSets();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.Parameter <em>Parameter</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Parameter</em>'.
	 * @see tools.refinery.language.model.problem.Parameter
	 * @generated
	 */
	EClass getParameter();

	/**
	 * Returns the meta object for the reference '{@link tools.refinery.language.model.problem.Parameter#getParameterType <em>Parameter Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Parameter Type</em>'.
	 * @see tools.refinery.language.model.problem.Parameter#getParameterType()
	 * @see #getParameter()
	 * @generated
	 */
	EReference getParameter_ParameterType();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.Parameter#getKind <em>Kind</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Kind</em>'.
	 * @see tools.refinery.language.model.problem.Parameter#getKind()
	 * @see #getParameter()
	 * @generated
	 */
	EAttribute getParameter_Kind();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.Variable <em>Variable</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Variable</em>'.
	 * @see tools.refinery.language.model.problem.Variable
	 * @generated
	 */
	EClass getVariable();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.Atom <em>Atom</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Atom</em>'.
	 * @see tools.refinery.language.model.problem.Atom
	 * @generated
	 */
	EClass getAtom();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.Atom#isTransitiveClosure <em>Transitive Closure</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Transitive Closure</em>'.
	 * @see tools.refinery.language.model.problem.Atom#isTransitiveClosure()
	 * @see #getAtom()
	 * @generated
	 */
	EAttribute getAtom_TransitiveClosure();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.Atom#getArguments <em>Arguments</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Arguments</em>'.
	 * @see tools.refinery.language.model.problem.Atom#getArguments()
	 * @see #getAtom()
	 * @generated
	 */
	EReference getAtom_Arguments();

	/**
	 * Returns the meta object for the reference '{@link tools.refinery.language.model.problem.Atom#getRelation <em>Relation</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Relation</em>'.
	 * @see tools.refinery.language.model.problem.Atom#getRelation()
	 * @see #getAtom()
	 * @generated
	 */
	EReference getAtom_Relation();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.ImplicitVariable <em>Implicit Variable</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Implicit Variable</em>'.
	 * @see tools.refinery.language.model.problem.ImplicitVariable
	 * @generated
	 */
	EClass getImplicitVariable();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.ExistentialQuantifier <em>Existential Quantifier</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Existential Quantifier</em>'.
	 * @see tools.refinery.language.model.problem.ExistentialQuantifier
	 * @generated
	 */
	EClass getExistentialQuantifier();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.ExistentialQuantifier#getImplicitVariables <em>Implicit Variables</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Implicit Variables</em>'.
	 * @see tools.refinery.language.model.problem.ExistentialQuantifier#getImplicitVariables()
	 * @see #getExistentialQuantifier()
	 * @generated
	 */
	EReference getExistentialQuantifier_ImplicitVariables();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.AbstractAssertion <em>Abstract Assertion</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Abstract Assertion</em>'.
	 * @see tools.refinery.language.model.problem.AbstractAssertion
	 * @generated
	 */
	EClass getAbstractAssertion();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.AbstractAssertion#getArguments <em>Arguments</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Arguments</em>'.
	 * @see tools.refinery.language.model.problem.AbstractAssertion#getArguments()
	 * @see #getAbstractAssertion()
	 * @generated
	 */
	EReference getAbstractAssertion_Arguments();

	/**
	 * Returns the meta object for the reference '{@link tools.refinery.language.model.problem.AbstractAssertion#getRelation <em>Relation</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Relation</em>'.
	 * @see tools.refinery.language.model.problem.AbstractAssertion#getRelation()
	 * @see #getAbstractAssertion()
	 * @generated
	 */
	EReference getAbstractAssertion_Relation();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.AbstractAssertion#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Value</em>'.
	 * @see tools.refinery.language.model.problem.AbstractAssertion#getValue()
	 * @see #getAbstractAssertion()
	 * @generated
	 */
	EReference getAbstractAssertion_Value();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.Node <em>Node</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Node</em>'.
	 * @see tools.refinery.language.model.problem.Node
	 * @generated
	 */
	EClass getNode();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.ScopeDeclaration <em>Scope Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Scope Declaration</em>'.
	 * @see tools.refinery.language.model.problem.ScopeDeclaration
	 * @generated
	 */
	EClass getScopeDeclaration();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.ScopeDeclaration#getTypeScopes <em>Type Scopes</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Type Scopes</em>'.
	 * @see tools.refinery.language.model.problem.ScopeDeclaration#getTypeScopes()
	 * @see #getScopeDeclaration()
	 * @generated
	 */
	EReference getScopeDeclaration_TypeScopes();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.Statement <em>Statement</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Statement</em>'.
	 * @see tools.refinery.language.model.problem.Statement
	 * @generated
	 */
	EClass getStatement();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.TypeScope <em>Type Scope</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Type Scope</em>'.
	 * @see tools.refinery.language.model.problem.TypeScope
	 * @generated
	 */
	EClass getTypeScope();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.TypeScope#isIncrement <em>Increment</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Increment</em>'.
	 * @see tools.refinery.language.model.problem.TypeScope#isIncrement()
	 * @see #getTypeScope()
	 * @generated
	 */
	EAttribute getTypeScope_Increment();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.TypeScope#getMultiplicity <em>Multiplicity</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Multiplicity</em>'.
	 * @see tools.refinery.language.model.problem.TypeScope#getMultiplicity()
	 * @see #getTypeScope()
	 * @generated
	 */
	EReference getTypeScope_Multiplicity();

	/**
	 * Returns the meta object for the reference '{@link tools.refinery.language.model.problem.TypeScope#getTargetType <em>Target Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Target Type</em>'.
	 * @see tools.refinery.language.model.problem.TypeScope#getTargetType()
	 * @see #getTypeScope()
	 * @generated
	 */
	EReference getTypeScope_TargetType();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.Multiplicity <em>Multiplicity</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Multiplicity</em>'.
	 * @see tools.refinery.language.model.problem.Multiplicity
	 * @generated
	 */
	EClass getMultiplicity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.RangeMultiplicity <em>Range Multiplicity</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Range Multiplicity</em>'.
	 * @see tools.refinery.language.model.problem.RangeMultiplicity
	 * @generated
	 */
	EClass getRangeMultiplicity();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.RangeMultiplicity#getLowerBound <em>Lower Bound</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Lower Bound</em>'.
	 * @see tools.refinery.language.model.problem.RangeMultiplicity#getLowerBound()
	 * @see #getRangeMultiplicity()
	 * @generated
	 */
	EAttribute getRangeMultiplicity_LowerBound();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.RangeMultiplicity#getUpperBound <em>Upper Bound</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Upper Bound</em>'.
	 * @see tools.refinery.language.model.problem.RangeMultiplicity#getUpperBound()
	 * @see #getRangeMultiplicity()
	 * @generated
	 */
	EAttribute getRangeMultiplicity_UpperBound();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.ExactMultiplicity <em>Exact Multiplicity</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Exact Multiplicity</em>'.
	 * @see tools.refinery.language.model.problem.ExactMultiplicity
	 * @generated
	 */
	EClass getExactMultiplicity();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.ExactMultiplicity#getExactValue <em>Exact Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Exact Value</em>'.
	 * @see tools.refinery.language.model.problem.ExactMultiplicity#getExactValue()
	 * @see #getExactMultiplicity()
	 * @generated
	 */
	EAttribute getExactMultiplicity_ExactValue();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.UnboundedMultiplicity <em>Unbounded Multiplicity</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Unbounded Multiplicity</em>'.
	 * @see tools.refinery.language.model.problem.UnboundedMultiplicity
	 * @generated
	 */
	EClass getUnboundedMultiplicity();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.EnumDeclaration <em>Enum Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Enum Declaration</em>'.
	 * @see tools.refinery.language.model.problem.EnumDeclaration
	 * @generated
	 */
	EClass getEnumDeclaration();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.EnumDeclaration#getLiterals <em>Literals</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Literals</em>'.
	 * @see tools.refinery.language.model.problem.EnumDeclaration#getLiterals()
	 * @see #getEnumDeclaration()
	 * @generated
	 */
	EReference getEnumDeclaration_Literals();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.VariableOrNode <em>Variable Or Node</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Variable Or Node</em>'.
	 * @see tools.refinery.language.model.problem.VariableOrNode
	 * @generated
	 */
	EClass getVariableOrNode();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.Constant <em>Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Constant</em>'.
	 * @see tools.refinery.language.model.problem.Constant
	 * @generated
	 */
	EClass getConstant();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.IntConstant <em>Int Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Int Constant</em>'.
	 * @see tools.refinery.language.model.problem.IntConstant
	 * @generated
	 */
	EClass getIntConstant();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.IntConstant#getIntValue <em>Int Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Int Value</em>'.
	 * @see tools.refinery.language.model.problem.IntConstant#getIntValue()
	 * @see #getIntConstant()
	 * @generated
	 */
	EAttribute getIntConstant_IntValue();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.RealConstant <em>Real Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Real Constant</em>'.
	 * @see tools.refinery.language.model.problem.RealConstant
	 * @generated
	 */
	EClass getRealConstant();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.RealConstant#getRealValue <em>Real Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Real Value</em>'.
	 * @see tools.refinery.language.model.problem.RealConstant#getRealValue()
	 * @see #getRealConstant()
	 * @generated
	 */
	EAttribute getRealConstant_RealValue();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.StringConstant <em>String Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>String Constant</em>'.
	 * @see tools.refinery.language.model.problem.StringConstant
	 * @generated
	 */
	EClass getStringConstant();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.StringConstant#getStringValue <em>String Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>String Value</em>'.
	 * @see tools.refinery.language.model.problem.StringConstant#getStringValue()
	 * @see #getStringConstant()
	 * @generated
	 */
	EAttribute getStringConstant_StringValue();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.NodeAssertionArgument <em>Node Assertion Argument</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Node Assertion Argument</em>'.
	 * @see tools.refinery.language.model.problem.NodeAssertionArgument
	 * @generated
	 */
	EClass getNodeAssertionArgument();

	/**
	 * Returns the meta object for the reference '{@link tools.refinery.language.model.problem.NodeAssertionArgument#getNode <em>Node</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Node</em>'.
	 * @see tools.refinery.language.model.problem.NodeAssertionArgument#getNode()
	 * @see #getNodeAssertionArgument()
	 * @generated
	 */
	EReference getNodeAssertionArgument_Node();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.AssertionArgument <em>Assertion Argument</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Assertion Argument</em>'.
	 * @see tools.refinery.language.model.problem.AssertionArgument
	 * @generated
	 */
	EClass getAssertionArgument();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.NodeDeclaration <em>Node Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Node Declaration</em>'.
	 * @see tools.refinery.language.model.problem.NodeDeclaration
	 * @generated
	 */
	EClass getNodeDeclaration();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.NodeDeclaration#getNodes <em>Nodes</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Nodes</em>'.
	 * @see tools.refinery.language.model.problem.NodeDeclaration#getNodes()
	 * @see #getNodeDeclaration()
	 * @generated
	 */
	EReference getNodeDeclaration_Nodes();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.NodeDeclaration#getKind <em>Kind</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Kind</em>'.
	 * @see tools.refinery.language.model.problem.NodeDeclaration#getKind()
	 * @see #getNodeDeclaration()
	 * @generated
	 */
	EAttribute getNodeDeclaration_Kind();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.WildcardAssertionArgument <em>Wildcard Assertion Argument</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Wildcard Assertion Argument</em>'.
	 * @see tools.refinery.language.model.problem.WildcardAssertionArgument
	 * @generated
	 */
	EClass getWildcardAssertionArgument();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.ParametricDefinition <em>Parametric Definition</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Parametric Definition</em>'.
	 * @see tools.refinery.language.model.problem.ParametricDefinition
	 * @generated
	 */
	EClass getParametricDefinition();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.ParametricDefinition#getParameters <em>Parameters</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Parameters</em>'.
	 * @see tools.refinery.language.model.problem.ParametricDefinition#getParameters()
	 * @see #getParametricDefinition()
	 * @generated
	 */
	EReference getParametricDefinition_Parameters();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.RuleDefinition <em>Rule Definition</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Rule Definition</em>'.
	 * @see tools.refinery.language.model.problem.RuleDefinition
	 * @generated
	 */
	EClass getRuleDefinition();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.RuleDefinition#getConsequents <em>Consequents</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Consequents</em>'.
	 * @see tools.refinery.language.model.problem.RuleDefinition#getConsequents()
	 * @see #getRuleDefinition()
	 * @generated
	 */
	EReference getRuleDefinition_Consequents();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.RuleDefinition#getPreconditions <em>Preconditions</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Preconditions</em>'.
	 * @see tools.refinery.language.model.problem.RuleDefinition#getPreconditions()
	 * @see #getRuleDefinition()
	 * @generated
	 */
	EReference getRuleDefinition_Preconditions();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.RuleDefinition#getKind <em>Kind</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Kind</em>'.
	 * @see tools.refinery.language.model.problem.RuleDefinition#getKind()
	 * @see #getRuleDefinition()
	 * @generated
	 */
	EAttribute getRuleDefinition_Kind();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.Consequent <em>Consequent</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Consequent</em>'.
	 * @see tools.refinery.language.model.problem.Consequent
	 * @generated
	 */
	EClass getConsequent();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.Consequent#getActions <em>Actions</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Actions</em>'.
	 * @see tools.refinery.language.model.problem.Consequent#getActions()
	 * @see #getConsequent()
	 * @generated
	 */
	EReference getConsequent_Actions();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.Action <em>Action</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Action</em>'.
	 * @see tools.refinery.language.model.problem.Action
	 * @generated
	 */
	EClass getAction();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.AssertionAction <em>Assertion Action</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Assertion Action</em>'.
	 * @see tools.refinery.language.model.problem.AssertionAction
	 * @generated
	 */
	EClass getAssertionAction();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.Expr <em>Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Expr</em>'.
	 * @see tools.refinery.language.model.problem.Expr
	 * @generated
	 */
	EClass getExpr();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.VariableOrNodeExpr <em>Variable Or Node Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Variable Or Node Expr</em>'.
	 * @see tools.refinery.language.model.problem.VariableOrNodeExpr
	 * @generated
	 */
	EClass getVariableOrNodeExpr();

	/**
	 * Returns the meta object for the reference '{@link tools.refinery.language.model.problem.VariableOrNodeExpr#getVariableOrNode <em>Variable Or Node</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Variable Or Node</em>'.
	 * @see tools.refinery.language.model.problem.VariableOrNodeExpr#getVariableOrNode()
	 * @see #getVariableOrNodeExpr()
	 * @generated
	 */
	EReference getVariableOrNodeExpr_VariableOrNode();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.VariableOrNodeExpr#getSingletonVariable <em>Singleton Variable</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Singleton Variable</em>'.
	 * @see tools.refinery.language.model.problem.VariableOrNodeExpr#getSingletonVariable()
	 * @see #getVariableOrNodeExpr()
	 * @generated
	 */
	EReference getVariableOrNodeExpr_SingletonVariable();

	/**
	 * Returns the meta object for the reference '{@link tools.refinery.language.model.problem.VariableOrNodeExpr#getRelation <em>Relation</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Relation</em>'.
	 * @see tools.refinery.language.model.problem.VariableOrNodeExpr#getRelation()
	 * @see #getVariableOrNodeExpr()
	 * @generated
	 */
	EReference getVariableOrNodeExpr_Relation();

	/**
	 * Returns the meta object for the reference '{@link tools.refinery.language.model.problem.VariableOrNodeExpr#getElement <em>Element</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Element</em>'.
	 * @see tools.refinery.language.model.problem.VariableOrNodeExpr#getElement()
	 * @see #getVariableOrNodeExpr()
	 * @generated
	 */
	EReference getVariableOrNodeExpr_Element();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.BinaryExpr <em>Binary Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Binary Expr</em>'.
	 * @see tools.refinery.language.model.problem.BinaryExpr
	 * @generated
	 */
	EClass getBinaryExpr();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.BinaryExpr#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see tools.refinery.language.model.problem.BinaryExpr#getLeft()
	 * @see #getBinaryExpr()
	 * @generated
	 */
	EReference getBinaryExpr_Left();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.BinaryExpr#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see tools.refinery.language.model.problem.BinaryExpr#getRight()
	 * @see #getBinaryExpr()
	 * @generated
	 */
	EReference getBinaryExpr_Right();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.UnaryExpr <em>Unary Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Unary Expr</em>'.
	 * @see tools.refinery.language.model.problem.UnaryExpr
	 * @generated
	 */
	EClass getUnaryExpr();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.UnaryExpr#getBody <em>Body</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Body</em>'.
	 * @see tools.refinery.language.model.problem.UnaryExpr#getBody()
	 * @see #getUnaryExpr()
	 * @generated
	 */
	EReference getUnaryExpr_Body();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.ArithmeticUnaryExpr <em>Arithmetic Unary Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Arithmetic Unary Expr</em>'.
	 * @see tools.refinery.language.model.problem.ArithmeticUnaryExpr
	 * @generated
	 */
	EClass getArithmeticUnaryExpr();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.ArithmeticUnaryExpr#getOp <em>Op</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Op</em>'.
	 * @see tools.refinery.language.model.problem.ArithmeticUnaryExpr#getOp()
	 * @see #getArithmeticUnaryExpr()
	 * @generated
	 */
	EAttribute getArithmeticUnaryExpr_Op();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.AggregationExpr <em>Aggregation Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Aggregation Expr</em>'.
	 * @see tools.refinery.language.model.problem.AggregationExpr
	 * @generated
	 */
	EClass getAggregationExpr();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.AggregationExpr#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Value</em>'.
	 * @see tools.refinery.language.model.problem.AggregationExpr#getValue()
	 * @see #getAggregationExpr()
	 * @generated
	 */
	EReference getAggregationExpr_Value();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.AggregationExpr#getCondition <em>Condition</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Condition</em>'.
	 * @see tools.refinery.language.model.problem.AggregationExpr#getCondition()
	 * @see #getAggregationExpr()
	 * @generated
	 */
	EReference getAggregationExpr_Condition();

	/**
	 * Returns the meta object for the reference '{@link tools.refinery.language.model.problem.AggregationExpr#getAggregator <em>Aggregator</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Aggregator</em>'.
	 * @see tools.refinery.language.model.problem.AggregationExpr#getAggregator()
	 * @see #getAggregationExpr()
	 * @generated
	 */
	EReference getAggregationExpr_Aggregator();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.ComparisonExpr <em>Comparison Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Comparison Expr</em>'.
	 * @see tools.refinery.language.model.problem.ComparisonExpr
	 * @generated
	 */
	EClass getComparisonExpr();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.ComparisonExpr#getOp <em>Op</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Op</em>'.
	 * @see tools.refinery.language.model.problem.ComparisonExpr#getOp()
	 * @see #getComparisonExpr()
	 * @generated
	 */
	EAttribute getComparisonExpr_Op();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.NegationExpr <em>Negation Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Negation Expr</em>'.
	 * @see tools.refinery.language.model.problem.NegationExpr
	 * @generated
	 */
	EClass getNegationExpr();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.FunctionDefinition <em>Function Definition</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Function Definition</em>'.
	 * @see tools.refinery.language.model.problem.FunctionDefinition
	 * @generated
	 */
	EClass getFunctionDefinition();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.FunctionDefinition#getCases <em>Cases</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Cases</em>'.
	 * @see tools.refinery.language.model.problem.FunctionDefinition#getCases()
	 * @see #getFunctionDefinition()
	 * @generated
	 */
	EReference getFunctionDefinition_Cases();

	/**
	 * Returns the meta object for the reference '{@link tools.refinery.language.model.problem.FunctionDefinition#getFunctionType <em>Function Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Function Type</em>'.
	 * @see tools.refinery.language.model.problem.FunctionDefinition#getFunctionType()
	 * @see #getFunctionDefinition()
	 * @generated
	 */
	EReference getFunctionDefinition_FunctionType();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.FunctionDefinition#isShadow <em>Shadow</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Shadow</em>'.
	 * @see tools.refinery.language.model.problem.FunctionDefinition#isShadow()
	 * @see #getFunctionDefinition()
	 * @generated
	 */
	EAttribute getFunctionDefinition_Shadow();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.FunctionDefinition#getComputedValue <em>Computed Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Computed Value</em>'.
	 * @see tools.refinery.language.model.problem.FunctionDefinition#getComputedValue()
	 * @see #getFunctionDefinition()
	 * @generated
	 */
	EReference getFunctionDefinition_ComputedValue();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.FunctionDefinition#getDomainPredicate <em>Domain Predicate</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Domain Predicate</em>'.
	 * @see tools.refinery.language.model.problem.FunctionDefinition#getDomainPredicate()
	 * @see #getFunctionDefinition()
	 * @generated
	 */
	EReference getFunctionDefinition_DomainPredicate();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.Conjunction <em>Conjunction</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Conjunction</em>'.
	 * @see tools.refinery.language.model.problem.Conjunction
	 * @generated
	 */
	EClass getConjunction();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.Conjunction#getLiterals <em>Literals</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Literals</em>'.
	 * @see tools.refinery.language.model.problem.Conjunction#getLiterals()
	 * @see #getConjunction()
	 * @generated
	 */
	EReference getConjunction_Literals();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.Case <em>Case</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Case</em>'.
	 * @see tools.refinery.language.model.problem.Case
	 * @generated
	 */
	EClass getCase();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.Case#getCondition <em>Condition</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Condition</em>'.
	 * @see tools.refinery.language.model.problem.Case#getCondition()
	 * @see #getCase()
	 * @generated
	 */
	EReference getCase_Condition();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.Case#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Value</em>'.
	 * @see tools.refinery.language.model.problem.Case#getValue()
	 * @see #getCase()
	 * @generated
	 */
	EReference getCase_Value();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.ArithmeticBinaryExpr <em>Arithmetic Binary Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Arithmetic Binary Expr</em>'.
	 * @see tools.refinery.language.model.problem.ArithmeticBinaryExpr
	 * @generated
	 */
	EClass getArithmeticBinaryExpr();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.ArithmeticBinaryExpr#getOp <em>Op</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Op</em>'.
	 * @see tools.refinery.language.model.problem.ArithmeticBinaryExpr#getOp()
	 * @see #getArithmeticBinaryExpr()
	 * @generated
	 */
	EAttribute getArithmeticBinaryExpr_Op();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.Relation <em>Relation</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Relation</em>'.
	 * @see tools.refinery.language.model.problem.Relation
	 * @generated
	 */
	EClass getRelation();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.RangeExpr <em>Range Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Range Expr</em>'.
	 * @see tools.refinery.language.model.problem.RangeExpr
	 * @generated
	 */
	EClass getRangeExpr();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.LogicConstant <em>Logic Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Logic Constant</em>'.
	 * @see tools.refinery.language.model.problem.LogicConstant
	 * @generated
	 */
	EClass getLogicConstant();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.LogicConstant#getLogicValue <em>Logic Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Logic Value</em>'.
	 * @see tools.refinery.language.model.problem.LogicConstant#getLogicValue()
	 * @see #getLogicConstant()
	 * @generated
	 */
	EAttribute getLogicConstant_LogicValue();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.ImportStatement <em>Import Statement</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Import Statement</em>'.
	 * @see tools.refinery.language.model.problem.ImportStatement
	 * @generated
	 */
	EClass getImportStatement();

	/**
	 * Returns the meta object for the reference '{@link tools.refinery.language.model.problem.ImportStatement#getImportedModule <em>Imported Module</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Imported Module</em>'.
	 * @see tools.refinery.language.model.problem.ImportStatement#getImportedModule()
	 * @see #getImportStatement()
	 * @generated
	 */
	EReference getImportStatement_ImportedModule();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.ImportStatement#getAlias <em>Alias</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Alias</em>'.
	 * @see tools.refinery.language.model.problem.ImportStatement#getAlias()
	 * @see #getImportStatement()
	 * @generated
	 */
	EAttribute getImportStatement_Alias();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.DatatypeDeclaration <em>Datatype Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Datatype Declaration</em>'.
	 * @see tools.refinery.language.model.problem.DatatypeDeclaration
	 * @generated
	 */
	EClass getDatatypeDeclaration();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.LatticeBinaryExpr <em>Lattice Binary Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Lattice Binary Expr</em>'.
	 * @see tools.refinery.language.model.problem.LatticeBinaryExpr
	 * @generated
	 */
	EClass getLatticeBinaryExpr();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.LatticeBinaryExpr#getOp <em>Op</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Op</em>'.
	 * @see tools.refinery.language.model.problem.LatticeBinaryExpr#getOp()
	 * @see #getLatticeBinaryExpr()
	 * @generated
	 */
	EAttribute getLatticeBinaryExpr_Op();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.AssignmentExpr <em>Assignment Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Assignment Expr</em>'.
	 * @see tools.refinery.language.model.problem.AssignmentExpr
	 * @generated
	 */
	EClass getAssignmentExpr();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.InfiniteConstant <em>Infinite Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Infinite Constant</em>'.
	 * @see tools.refinery.language.model.problem.InfiniteConstant
	 * @generated
	 */
	EClass getInfiniteConstant();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.AggregatorDeclaration <em>Aggregator Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Aggregator Declaration</em>'.
	 * @see tools.refinery.language.model.problem.AggregatorDeclaration
	 * @generated
	 */
	EClass getAggregatorDeclaration();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.ModalExpr <em>Modal Expr</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Modal Expr</em>'.
	 * @see tools.refinery.language.model.problem.ModalExpr
	 * @generated
	 */
	EClass getModalExpr();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.ModalExpr#getConcreteness <em>Concreteness</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Concreteness</em>'.
	 * @see tools.refinery.language.model.problem.ModalExpr#getConcreteness()
	 * @see #getModalExpr()
	 * @generated
	 */
	EAttribute getModalExpr_Concreteness();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.ModalExpr#getModality <em>Modality</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Modality</em>'.
	 * @see tools.refinery.language.model.problem.ModalExpr#getModality()
	 * @see #getModalExpr()
	 * @generated
	 */
	EAttribute getModalExpr_Modality();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.Assertion <em>Assertion</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Assertion</em>'.
	 * @see tools.refinery.language.model.problem.Assertion
	 * @generated
	 */
	EClass getAssertion();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.Assertion#isDefault <em>Default</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Default</em>'.
	 * @see tools.refinery.language.model.problem.Assertion#isDefault()
	 * @see #getAssertion()
	 * @generated
	 */
	EAttribute getAssertion_Default();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.AnnotatedElement <em>Annotated Element</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Annotated Element</em>'.
	 * @see tools.refinery.language.model.problem.AnnotatedElement
	 * @generated
	 */
	EClass getAnnotatedElement();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.AnnotatedElement#getAnnotations <em>Annotations</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Annotations</em>'.
	 * @see tools.refinery.language.model.problem.AnnotatedElement#getAnnotations()
	 * @see #getAnnotatedElement()
	 * @generated
	 */
	EReference getAnnotatedElement_Annotations();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.AnnotationContainer <em>Annotation Container</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Annotation Container</em>'.
	 * @see tools.refinery.language.model.problem.AnnotationContainer
	 * @generated
	 */
	EClass getAnnotationContainer();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.AnnotationContainer#getAnnotations <em>Annotations</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Annotations</em>'.
	 * @see tools.refinery.language.model.problem.AnnotationContainer#getAnnotations()
	 * @see #getAnnotationContainer()
	 * @generated
	 */
	EReference getAnnotationContainer_Annotations();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.AnnotationDeclaration <em>Annotation Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Annotation Declaration</em>'.
	 * @see tools.refinery.language.model.problem.AnnotationDeclaration
	 * @generated
	 */
	EClass getAnnotationDeclaration();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.Annotation <em>Annotation</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Annotation</em>'.
	 * @see tools.refinery.language.model.problem.Annotation
	 * @generated
	 */
	EClass getAnnotation();

	/**
	 * Returns the meta object for the reference '{@link tools.refinery.language.model.problem.Annotation#getDeclaration <em>Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Declaration</em>'.
	 * @see tools.refinery.language.model.problem.Annotation#getDeclaration()
	 * @see #getAnnotation()
	 * @generated
	 */
	EReference getAnnotation_Declaration();

	/**
	 * Returns the meta object for the containment reference list '{@link tools.refinery.language.model.problem.Annotation#getArguments <em>Arguments</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Arguments</em>'.
	 * @see tools.refinery.language.model.problem.Annotation#getArguments()
	 * @see #getAnnotation()
	 * @generated
	 */
	EReference getAnnotation_Arguments();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.AnnotationArgument <em>Annotation Argument</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Annotation Argument</em>'.
	 * @see tools.refinery.language.model.problem.AnnotationArgument
	 * @generated
	 */
	EClass getAnnotationArgument();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.AnnotationArgument#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Value</em>'.
	 * @see tools.refinery.language.model.problem.AnnotationArgument#getValue()
	 * @see #getAnnotationArgument()
	 * @generated
	 */
	EReference getAnnotationArgument_Value();

	/**
	 * Returns the meta object for the reference '{@link tools.refinery.language.model.problem.AnnotationArgument#getParameter <em>Parameter</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Parameter</em>'.
	 * @see tools.refinery.language.model.problem.AnnotationArgument#getParameter()
	 * @see #getAnnotationArgument()
	 * @generated
	 */
	EReference getAnnotationArgument_Parameter();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.TopLevelAnnotation <em>Top Level Annotation</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Top Level Annotation</em>'.
	 * @see tools.refinery.language.model.problem.TopLevelAnnotation
	 * @generated
	 */
	EClass getTopLevelAnnotation();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.TopLevelAnnotation#getAnnotation <em>Annotation</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Annotation</em>'.
	 * @see tools.refinery.language.model.problem.TopLevelAnnotation#getAnnotation()
	 * @see #getTopLevelAnnotation()
	 * @generated
	 */
	EReference getTopLevelAnnotation_Annotation();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.OverloadedDeclaration <em>Overloaded Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Overloaded Declaration</em>'.
	 * @see tools.refinery.language.model.problem.OverloadedDeclaration
	 * @generated
	 */
	EClass getOverloadedDeclaration();

	/**
	 * Returns the meta object for the attribute '{@link tools.refinery.language.model.problem.OverloadedDeclaration#isShadow <em>Shadow</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Shadow</em>'.
	 * @see tools.refinery.language.model.problem.OverloadedDeclaration#isShadow()
	 * @see #getOverloadedDeclaration()
	 * @generated
	 */
	EAttribute getOverloadedDeclaration_Shadow();

	/**
	 * Returns the meta object for class '{@link tools.refinery.language.model.problem.TheoryAction <em>Theory Action</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Theory Action</em>'.
	 * @see tools.refinery.language.model.problem.TheoryAction
	 * @generated
	 */
	EClass getTheoryAction();

	/**
	 * Returns the meta object for the containment reference '{@link tools.refinery.language.model.problem.TheoryAction#getTerm <em>Term</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Term</em>'.
	 * @see tools.refinery.language.model.problem.TheoryAction#getTerm()
	 * @see #getTheoryAction()
	 * @generated
	 */
	EReference getTheoryAction_Term();

	/**
	 * Returns the meta object for enum '{@link tools.refinery.language.model.problem.LogicValue <em>Logic Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Logic Value</em>'.
	 * @see tools.refinery.language.model.problem.LogicValue
	 * @generated
	 */
	EEnum getLogicValue();

	/**
	 * Returns the meta object for enum '{@link tools.refinery.language.model.problem.ComparisonOp <em>Comparison Op</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Comparison Op</em>'.
	 * @see tools.refinery.language.model.problem.ComparisonOp
	 * @generated
	 */
	EEnum getComparisonOp();

	/**
	 * Returns the meta object for enum '{@link tools.refinery.language.model.problem.ReferenceKind <em>Reference Kind</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Reference Kind</em>'.
	 * @see tools.refinery.language.model.problem.ReferenceKind
	 * @generated
	 */
	EEnum getReferenceKind();

	/**
	 * Returns the meta object for enum '{@link tools.refinery.language.model.problem.UnaryOp <em>Unary Op</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Unary Op</em>'.
	 * @see tools.refinery.language.model.problem.UnaryOp
	 * @generated
	 */
	EEnum getUnaryOp();

	/**
	 * Returns the meta object for enum '{@link tools.refinery.language.model.problem.BinaryOp <em>Binary Op</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Binary Op</em>'.
	 * @see tools.refinery.language.model.problem.BinaryOp
	 * @generated
	 */
	EEnum getBinaryOp();

	/**
	 * Returns the meta object for enum '{@link tools.refinery.language.model.problem.ModuleKind <em>Module Kind</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Module Kind</em>'.
	 * @see tools.refinery.language.model.problem.ModuleKind
	 * @generated
	 */
	EEnum getModuleKind();

	/**
	 * Returns the meta object for enum '{@link tools.refinery.language.model.problem.NodeKind <em>Node Kind</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Node Kind</em>'.
	 * @see tools.refinery.language.model.problem.NodeKind
	 * @generated
	 */
	EEnum getNodeKind();

	/**
	 * Returns the meta object for enum '{@link tools.refinery.language.model.problem.LatticeBinaryOp <em>Lattice Binary Op</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Lattice Binary Op</em>'.
	 * @see tools.refinery.language.model.problem.LatticeBinaryOp
	 * @generated
	 */
	EEnum getLatticeBinaryOp();

	/**
	 * Returns the meta object for enum '{@link tools.refinery.language.model.problem.Modality <em>Modality</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Modality</em>'.
	 * @see tools.refinery.language.model.problem.Modality
	 * @generated
	 */
	EEnum getModality();

	/**
	 * Returns the meta object for enum '{@link tools.refinery.language.model.problem.Concreteness <em>Concreteness</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Concreteness</em>'.
	 * @see tools.refinery.language.model.problem.Concreteness
	 * @generated
	 */
	EEnum getConcreteness();

	/**
	 * Returns the meta object for enum '{@link tools.refinery.language.model.problem.RuleKind <em>Rule Kind</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Rule Kind</em>'.
	 * @see tools.refinery.language.model.problem.RuleKind
	 * @generated
	 */
	EEnum getRuleKind();

	/**
	 * Returns the meta object for enum '{@link tools.refinery.language.model.problem.PredicateKind <em>Predicate Kind</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Predicate Kind</em>'.
	 * @see tools.refinery.language.model.problem.PredicateKind
	 * @generated
	 */
	EEnum getPredicateKind();

	/**
	 * Returns the meta object for enum '{@link tools.refinery.language.model.problem.ParameterKind <em>Parameter Kind</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Parameter Kind</em>'.
	 * @see tools.refinery.language.model.problem.ParameterKind
	 * @generated
	 */
	EEnum getParameterKind();

	/**
	 * Returns the factory that creates the instances of the model.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the factory that creates the instances of the model.
	 * @generated
	 */
	ProblemFactory getProblemFactory();

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
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.ProblemImpl <em>Problem</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.ProblemImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getProblem()
		 * @generated
		 */
		EClass PROBLEM = eINSTANCE.getProblem();

		/**
		 * The meta object literal for the '<em><b>Nodes</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PROBLEM__NODES = eINSTANCE.getProblem_Nodes();

		/**
		 * The meta object literal for the '<em><b>Statements</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PROBLEM__STATEMENTS = eINSTANCE.getProblem_Statements();

		/**
		 * The meta object literal for the '<em><b>Kind</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute PROBLEM__KIND = eINSTANCE.getProblem_Kind();

		/**
		 * The meta object literal for the '<em><b>Explicit Kind</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute PROBLEM__EXPLICIT_KIND = eINSTANCE.getProblem_ExplicitKind();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.ClassDeclarationImpl <em>Class Declaration</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.ClassDeclarationImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getClassDeclaration()
		 * @generated
		 */
		EClass CLASS_DECLARATION = eINSTANCE.getClassDeclaration();

		/**
		 * The meta object literal for the '<em><b>Abstract</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute CLASS_DECLARATION__ABSTRACT = eINSTANCE.getClassDeclaration_Abstract();

		/**
		 * The meta object literal for the '<em><b>Feature Declarations</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CLASS_DECLARATION__FEATURE_DECLARATIONS = eINSTANCE.getClassDeclaration_FeatureDeclarations();

		/**
		 * The meta object literal for the '<em><b>New Node</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CLASS_DECLARATION__NEW_NODE = eINSTANCE.getClassDeclaration_NewNode();

		/**
		 * The meta object literal for the '<em><b>Super Types</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CLASS_DECLARATION__SUPER_TYPES = eINSTANCE.getClassDeclaration_SuperTypes();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.ReferenceDeclarationImpl <em>Reference Declaration</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.ReferenceDeclarationImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getReferenceDeclaration()
		 * @generated
		 */
		EClass REFERENCE_DECLARATION = eINSTANCE.getReferenceDeclaration();

		/**
		 * The meta object literal for the '<em><b>Opposite</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference REFERENCE_DECLARATION__OPPOSITE = eINSTANCE.getReferenceDeclaration_Opposite();

		/**
		 * The meta object literal for the '<em><b>Multiplicity</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference REFERENCE_DECLARATION__MULTIPLICITY = eINSTANCE.getReferenceDeclaration_Multiplicity();

		/**
		 * The meta object literal for the '<em><b>Kind</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute REFERENCE_DECLARATION__KIND = eINSTANCE.getReferenceDeclaration_Kind();

		/**
		 * The meta object literal for the '<em><b>Reference Type</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference REFERENCE_DECLARATION__REFERENCE_TYPE = eINSTANCE.getReferenceDeclaration_ReferenceType();

		/**
		 * The meta object literal for the '<em><b>Invalid Multiplicity</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference REFERENCE_DECLARATION__INVALID_MULTIPLICITY = eINSTANCE.getReferenceDeclaration_InvalidMultiplicity();

		/**
		 * The meta object literal for the '<em><b>Super Sets</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference REFERENCE_DECLARATION__SUPER_SETS = eINSTANCE.getReferenceDeclaration_SuperSets();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.NamedElementImpl <em>Named Element</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.NamedElementImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getNamedElement()
		 * @generated
		 */
		EClass NAMED_ELEMENT = eINSTANCE.getNamedElement();

		/**
		 * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute NAMED_ELEMENT__NAME = eINSTANCE.getNamedElement_Name();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.PredicateDefinitionImpl <em>Predicate Definition</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.PredicateDefinitionImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getPredicateDefinition()
		 * @generated
		 */
		EClass PREDICATE_DEFINITION = eINSTANCE.getPredicateDefinition();

		/**
		 * The meta object literal for the '<em><b>Bodies</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PREDICATE_DEFINITION__BODIES = eINSTANCE.getPredicateDefinition_Bodies();

		/**
		 * The meta object literal for the '<em><b>Kind</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute PREDICATE_DEFINITION__KIND = eINSTANCE.getPredicateDefinition_Kind();

		/**
		 * The meta object literal for the '<em><b>Computed Value</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PREDICATE_DEFINITION__COMPUTED_VALUE = eINSTANCE.getPredicateDefinition_ComputedValue();

		/**
		 * The meta object literal for the '<em><b>Super Sets</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PREDICATE_DEFINITION__SUPER_SETS = eINSTANCE.getPredicateDefinition_SuperSets();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.ParameterImpl <em>Parameter</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.ParameterImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getParameter()
		 * @generated
		 */
		EClass PARAMETER = eINSTANCE.getParameter();

		/**
		 * The meta object literal for the '<em><b>Parameter Type</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PARAMETER__PARAMETER_TYPE = eINSTANCE.getParameter_ParameterType();

		/**
		 * The meta object literal for the '<em><b>Kind</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute PARAMETER__KIND = eINSTANCE.getParameter_Kind();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.VariableImpl <em>Variable</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.VariableImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getVariable()
		 * @generated
		 */
		EClass VARIABLE = eINSTANCE.getVariable();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.AtomImpl <em>Atom</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.AtomImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAtom()
		 * @generated
		 */
		EClass ATOM = eINSTANCE.getAtom();

		/**
		 * The meta object literal for the '<em><b>Transitive Closure</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute ATOM__TRANSITIVE_CLOSURE = eINSTANCE.getAtom_TransitiveClosure();

		/**
		 * The meta object literal for the '<em><b>Arguments</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ATOM__ARGUMENTS = eINSTANCE.getAtom_Arguments();

		/**
		 * The meta object literal for the '<em><b>Relation</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ATOM__RELATION = eINSTANCE.getAtom_Relation();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.ImplicitVariableImpl <em>Implicit Variable</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.ImplicitVariableImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getImplicitVariable()
		 * @generated
		 */
		EClass IMPLICIT_VARIABLE = eINSTANCE.getImplicitVariable();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.ExistentialQuantifier <em>Existential Quantifier</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.ExistentialQuantifier
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getExistentialQuantifier()
		 * @generated
		 */
		EClass EXISTENTIAL_QUANTIFIER = eINSTANCE.getExistentialQuantifier();

		/**
		 * The meta object literal for the '<em><b>Implicit Variables</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference EXISTENTIAL_QUANTIFIER__IMPLICIT_VARIABLES = eINSTANCE.getExistentialQuantifier_ImplicitVariables();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.AbstractAssertionImpl <em>Abstract Assertion</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.AbstractAssertionImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAbstractAssertion()
		 * @generated
		 */
		EClass ABSTRACT_ASSERTION = eINSTANCE.getAbstractAssertion();

		/**
		 * The meta object literal for the '<em><b>Arguments</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ABSTRACT_ASSERTION__ARGUMENTS = eINSTANCE.getAbstractAssertion_Arguments();

		/**
		 * The meta object literal for the '<em><b>Relation</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ABSTRACT_ASSERTION__RELATION = eINSTANCE.getAbstractAssertion_Relation();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ABSTRACT_ASSERTION__VALUE = eINSTANCE.getAbstractAssertion_Value();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.NodeImpl <em>Node</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.NodeImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getNode()
		 * @generated
		 */
		EClass NODE = eINSTANCE.getNode();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.ScopeDeclarationImpl <em>Scope Declaration</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.ScopeDeclarationImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getScopeDeclaration()
		 * @generated
		 */
		EClass SCOPE_DECLARATION = eINSTANCE.getScopeDeclaration();

		/**
		 * The meta object literal for the '<em><b>Type Scopes</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference SCOPE_DECLARATION__TYPE_SCOPES = eINSTANCE.getScopeDeclaration_TypeScopes();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.Statement <em>Statement</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.Statement
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getStatement()
		 * @generated
		 */
		EClass STATEMENT = eINSTANCE.getStatement();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.TypeScopeImpl <em>Type Scope</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.TypeScopeImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getTypeScope()
		 * @generated
		 */
		EClass TYPE_SCOPE = eINSTANCE.getTypeScope();

		/**
		 * The meta object literal for the '<em><b>Increment</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute TYPE_SCOPE__INCREMENT = eINSTANCE.getTypeScope_Increment();

		/**
		 * The meta object literal for the '<em><b>Multiplicity</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference TYPE_SCOPE__MULTIPLICITY = eINSTANCE.getTypeScope_Multiplicity();

		/**
		 * The meta object literal for the '<em><b>Target Type</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference TYPE_SCOPE__TARGET_TYPE = eINSTANCE.getTypeScope_TargetType();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.MultiplicityImpl <em>Multiplicity</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.MultiplicityImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getMultiplicity()
		 * @generated
		 */
		EClass MULTIPLICITY = eINSTANCE.getMultiplicity();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.RangeMultiplicityImpl <em>Range Multiplicity</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.RangeMultiplicityImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getRangeMultiplicity()
		 * @generated
		 */
		EClass RANGE_MULTIPLICITY = eINSTANCE.getRangeMultiplicity();

		/**
		 * The meta object literal for the '<em><b>Lower Bound</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute RANGE_MULTIPLICITY__LOWER_BOUND = eINSTANCE.getRangeMultiplicity_LowerBound();

		/**
		 * The meta object literal for the '<em><b>Upper Bound</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute RANGE_MULTIPLICITY__UPPER_BOUND = eINSTANCE.getRangeMultiplicity_UpperBound();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.ExactMultiplicityImpl <em>Exact Multiplicity</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.ExactMultiplicityImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getExactMultiplicity()
		 * @generated
		 */
		EClass EXACT_MULTIPLICITY = eINSTANCE.getExactMultiplicity();

		/**
		 * The meta object literal for the '<em><b>Exact Value</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute EXACT_MULTIPLICITY__EXACT_VALUE = eINSTANCE.getExactMultiplicity_ExactValue();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.UnboundedMultiplicityImpl <em>Unbounded Multiplicity</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.UnboundedMultiplicityImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getUnboundedMultiplicity()
		 * @generated
		 */
		EClass UNBOUNDED_MULTIPLICITY = eINSTANCE.getUnboundedMultiplicity();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.EnumDeclarationImpl <em>Enum Declaration</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.EnumDeclarationImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getEnumDeclaration()
		 * @generated
		 */
		EClass ENUM_DECLARATION = eINSTANCE.getEnumDeclaration();

		/**
		 * The meta object literal for the '<em><b>Literals</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ENUM_DECLARATION__LITERALS = eINSTANCE.getEnumDeclaration_Literals();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.VariableOrNodeImpl <em>Variable Or Node</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.VariableOrNodeImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getVariableOrNode()
		 * @generated
		 */
		EClass VARIABLE_OR_NODE = eINSTANCE.getVariableOrNode();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.ConstantImpl <em>Constant</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.ConstantImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getConstant()
		 * @generated
		 */
		EClass CONSTANT = eINSTANCE.getConstant();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.IntConstantImpl <em>Int Constant</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.IntConstantImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getIntConstant()
		 * @generated
		 */
		EClass INT_CONSTANT = eINSTANCE.getIntConstant();

		/**
		 * The meta object literal for the '<em><b>Int Value</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute INT_CONSTANT__INT_VALUE = eINSTANCE.getIntConstant_IntValue();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.RealConstantImpl <em>Real Constant</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.RealConstantImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getRealConstant()
		 * @generated
		 */
		EClass REAL_CONSTANT = eINSTANCE.getRealConstant();

		/**
		 * The meta object literal for the '<em><b>Real Value</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute REAL_CONSTANT__REAL_VALUE = eINSTANCE.getRealConstant_RealValue();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.StringConstantImpl <em>String Constant</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.StringConstantImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getStringConstant()
		 * @generated
		 */
		EClass STRING_CONSTANT = eINSTANCE.getStringConstant();

		/**
		 * The meta object literal for the '<em><b>String Value</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute STRING_CONSTANT__STRING_VALUE = eINSTANCE.getStringConstant_StringValue();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.NodeAssertionArgumentImpl <em>Node Assertion Argument</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.NodeAssertionArgumentImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getNodeAssertionArgument()
		 * @generated
		 */
		EClass NODE_ASSERTION_ARGUMENT = eINSTANCE.getNodeAssertionArgument();

		/**
		 * The meta object literal for the '<em><b>Node</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference NODE_ASSERTION_ARGUMENT__NODE = eINSTANCE.getNodeAssertionArgument_Node();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.AssertionArgumentImpl <em>Assertion Argument</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.AssertionArgumentImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAssertionArgument()
		 * @generated
		 */
		EClass ASSERTION_ARGUMENT = eINSTANCE.getAssertionArgument();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.NodeDeclarationImpl <em>Node Declaration</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.NodeDeclarationImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getNodeDeclaration()
		 * @generated
		 */
		EClass NODE_DECLARATION = eINSTANCE.getNodeDeclaration();

		/**
		 * The meta object literal for the '<em><b>Nodes</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference NODE_DECLARATION__NODES = eINSTANCE.getNodeDeclaration_Nodes();

		/**
		 * The meta object literal for the '<em><b>Kind</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute NODE_DECLARATION__KIND = eINSTANCE.getNodeDeclaration_Kind();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.WildcardAssertionArgumentImpl <em>Wildcard Assertion Argument</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.WildcardAssertionArgumentImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getWildcardAssertionArgument()
		 * @generated
		 */
		EClass WILDCARD_ASSERTION_ARGUMENT = eINSTANCE.getWildcardAssertionArgument();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.ParametricDefinition <em>Parametric Definition</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.ParametricDefinition
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getParametricDefinition()
		 * @generated
		 */
		EClass PARAMETRIC_DEFINITION = eINSTANCE.getParametricDefinition();

		/**
		 * The meta object literal for the '<em><b>Parameters</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PARAMETRIC_DEFINITION__PARAMETERS = eINSTANCE.getParametricDefinition_Parameters();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.RuleDefinitionImpl <em>Rule Definition</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.RuleDefinitionImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getRuleDefinition()
		 * @generated
		 */
		EClass RULE_DEFINITION = eINSTANCE.getRuleDefinition();

		/**
		 * The meta object literal for the '<em><b>Consequents</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference RULE_DEFINITION__CONSEQUENTS = eINSTANCE.getRuleDefinition_Consequents();

		/**
		 * The meta object literal for the '<em><b>Preconditions</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference RULE_DEFINITION__PRECONDITIONS = eINSTANCE.getRuleDefinition_Preconditions();

		/**
		 * The meta object literal for the '<em><b>Kind</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute RULE_DEFINITION__KIND = eINSTANCE.getRuleDefinition_Kind();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.ConsequentImpl <em>Consequent</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.ConsequentImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getConsequent()
		 * @generated
		 */
		EClass CONSEQUENT = eINSTANCE.getConsequent();

		/**
		 * The meta object literal for the '<em><b>Actions</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CONSEQUENT__ACTIONS = eINSTANCE.getConsequent_Actions();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.Action <em>Action</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.Action
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAction()
		 * @generated
		 */
		EClass ACTION = eINSTANCE.getAction();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.AssertionActionImpl <em>Assertion Action</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.AssertionActionImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAssertionAction()
		 * @generated
		 */
		EClass ASSERTION_ACTION = eINSTANCE.getAssertionAction();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.ExprImpl <em>Expr</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.ExprImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getExpr()
		 * @generated
		 */
		EClass EXPR = eINSTANCE.getExpr();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.VariableOrNodeExprImpl <em>Variable Or Node Expr</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.VariableOrNodeExprImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getVariableOrNodeExpr()
		 * @generated
		 */
		EClass VARIABLE_OR_NODE_EXPR = eINSTANCE.getVariableOrNodeExpr();

		/**
		 * The meta object literal for the '<em><b>Variable Or Node</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference VARIABLE_OR_NODE_EXPR__VARIABLE_OR_NODE = eINSTANCE.getVariableOrNodeExpr_VariableOrNode();

		/**
		 * The meta object literal for the '<em><b>Singleton Variable</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference VARIABLE_OR_NODE_EXPR__SINGLETON_VARIABLE = eINSTANCE.getVariableOrNodeExpr_SingletonVariable();

		/**
		 * The meta object literal for the '<em><b>Relation</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference VARIABLE_OR_NODE_EXPR__RELATION = eINSTANCE.getVariableOrNodeExpr_Relation();

		/**
		 * The meta object literal for the '<em><b>Element</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference VARIABLE_OR_NODE_EXPR__ELEMENT = eINSTANCE.getVariableOrNodeExpr_Element();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.BinaryExprImpl <em>Binary Expr</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.BinaryExprImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getBinaryExpr()
		 * @generated
		 */
		EClass BINARY_EXPR = eINSTANCE.getBinaryExpr();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference BINARY_EXPR__LEFT = eINSTANCE.getBinaryExpr_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference BINARY_EXPR__RIGHT = eINSTANCE.getBinaryExpr_Right();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.UnaryExprImpl <em>Unary Expr</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.UnaryExprImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getUnaryExpr()
		 * @generated
		 */
		EClass UNARY_EXPR = eINSTANCE.getUnaryExpr();

		/**
		 * The meta object literal for the '<em><b>Body</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference UNARY_EXPR__BODY = eINSTANCE.getUnaryExpr_Body();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.ArithmeticUnaryExprImpl <em>Arithmetic Unary Expr</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.ArithmeticUnaryExprImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getArithmeticUnaryExpr()
		 * @generated
		 */
		EClass ARITHMETIC_UNARY_EXPR = eINSTANCE.getArithmeticUnaryExpr();

		/**
		 * The meta object literal for the '<em><b>Op</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute ARITHMETIC_UNARY_EXPR__OP = eINSTANCE.getArithmeticUnaryExpr_Op();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.AggregationExprImpl <em>Aggregation Expr</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.AggregationExprImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAggregationExpr()
		 * @generated
		 */
		EClass AGGREGATION_EXPR = eINSTANCE.getAggregationExpr();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference AGGREGATION_EXPR__VALUE = eINSTANCE.getAggregationExpr_Value();

		/**
		 * The meta object literal for the '<em><b>Condition</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference AGGREGATION_EXPR__CONDITION = eINSTANCE.getAggregationExpr_Condition();

		/**
		 * The meta object literal for the '<em><b>Aggregator</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference AGGREGATION_EXPR__AGGREGATOR = eINSTANCE.getAggregationExpr_Aggregator();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.ComparisonExprImpl <em>Comparison Expr</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.ComparisonExprImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getComparisonExpr()
		 * @generated
		 */
		EClass COMPARISON_EXPR = eINSTANCE.getComparisonExpr();

		/**
		 * The meta object literal for the '<em><b>Op</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute COMPARISON_EXPR__OP = eINSTANCE.getComparisonExpr_Op();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.NegationExprImpl <em>Negation Expr</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.NegationExprImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getNegationExpr()
		 * @generated
		 */
		EClass NEGATION_EXPR = eINSTANCE.getNegationExpr();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.FunctionDefinitionImpl <em>Function Definition</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.FunctionDefinitionImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getFunctionDefinition()
		 * @generated
		 */
		EClass FUNCTION_DEFINITION = eINSTANCE.getFunctionDefinition();

		/**
		 * The meta object literal for the '<em><b>Cases</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FUNCTION_DEFINITION__CASES = eINSTANCE.getFunctionDefinition_Cases();

		/**
		 * The meta object literal for the '<em><b>Function Type</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FUNCTION_DEFINITION__FUNCTION_TYPE = eINSTANCE.getFunctionDefinition_FunctionType();

		/**
		 * The meta object literal for the '<em><b>Shadow</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute FUNCTION_DEFINITION__SHADOW = eINSTANCE.getFunctionDefinition_Shadow();

		/**
		 * The meta object literal for the '<em><b>Computed Value</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FUNCTION_DEFINITION__COMPUTED_VALUE = eINSTANCE.getFunctionDefinition_ComputedValue();

		/**
		 * The meta object literal for the '<em><b>Domain Predicate</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FUNCTION_DEFINITION__DOMAIN_PREDICATE = eINSTANCE.getFunctionDefinition_DomainPredicate();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.ConjunctionImpl <em>Conjunction</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.ConjunctionImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getConjunction()
		 * @generated
		 */
		EClass CONJUNCTION = eINSTANCE.getConjunction();

		/**
		 * The meta object literal for the '<em><b>Literals</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CONJUNCTION__LITERALS = eINSTANCE.getConjunction_Literals();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.CaseImpl <em>Case</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.CaseImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getCase()
		 * @generated
		 */
		EClass CASE = eINSTANCE.getCase();

		/**
		 * The meta object literal for the '<em><b>Condition</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CASE__CONDITION = eINSTANCE.getCase_Condition();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CASE__VALUE = eINSTANCE.getCase_Value();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.ArithmeticBinaryExprImpl <em>Arithmetic Binary Expr</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.ArithmeticBinaryExprImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getArithmeticBinaryExpr()
		 * @generated
		 */
		EClass ARITHMETIC_BINARY_EXPR = eINSTANCE.getArithmeticBinaryExpr();

		/**
		 * The meta object literal for the '<em><b>Op</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute ARITHMETIC_BINARY_EXPR__OP = eINSTANCE.getArithmeticBinaryExpr_Op();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.RelationImpl <em>Relation</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.RelationImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getRelation()
		 * @generated
		 */
		EClass RELATION = eINSTANCE.getRelation();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.RangeExprImpl <em>Range Expr</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.RangeExprImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getRangeExpr()
		 * @generated
		 */
		EClass RANGE_EXPR = eINSTANCE.getRangeExpr();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.LogicConstantImpl <em>Logic Constant</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.LogicConstantImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getLogicConstant()
		 * @generated
		 */
		EClass LOGIC_CONSTANT = eINSTANCE.getLogicConstant();

		/**
		 * The meta object literal for the '<em><b>Logic Value</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute LOGIC_CONSTANT__LOGIC_VALUE = eINSTANCE.getLogicConstant_LogicValue();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.ImportStatementImpl <em>Import Statement</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.ImportStatementImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getImportStatement()
		 * @generated
		 */
		EClass IMPORT_STATEMENT = eINSTANCE.getImportStatement();

		/**
		 * The meta object literal for the '<em><b>Imported Module</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference IMPORT_STATEMENT__IMPORTED_MODULE = eINSTANCE.getImportStatement_ImportedModule();

		/**
		 * The meta object literal for the '<em><b>Alias</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute IMPORT_STATEMENT__ALIAS = eINSTANCE.getImportStatement_Alias();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.DatatypeDeclarationImpl <em>Datatype Declaration</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.DatatypeDeclarationImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getDatatypeDeclaration()
		 * @generated
		 */
		EClass DATATYPE_DECLARATION = eINSTANCE.getDatatypeDeclaration();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.LatticeBinaryExprImpl <em>Lattice Binary Expr</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.LatticeBinaryExprImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getLatticeBinaryExpr()
		 * @generated
		 */
		EClass LATTICE_BINARY_EXPR = eINSTANCE.getLatticeBinaryExpr();

		/**
		 * The meta object literal for the '<em><b>Op</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute LATTICE_BINARY_EXPR__OP = eINSTANCE.getLatticeBinaryExpr_Op();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.AssignmentExprImpl <em>Assignment Expr</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.AssignmentExprImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAssignmentExpr()
		 * @generated
		 */
		EClass ASSIGNMENT_EXPR = eINSTANCE.getAssignmentExpr();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.InfiniteConstantImpl <em>Infinite Constant</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.InfiniteConstantImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getInfiniteConstant()
		 * @generated
		 */
		EClass INFINITE_CONSTANT = eINSTANCE.getInfiniteConstant();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.AggregatorDeclarationImpl <em>Aggregator Declaration</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.AggregatorDeclarationImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAggregatorDeclaration()
		 * @generated
		 */
		EClass AGGREGATOR_DECLARATION = eINSTANCE.getAggregatorDeclaration();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.ModalExprImpl <em>Modal Expr</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.ModalExprImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getModalExpr()
		 * @generated
		 */
		EClass MODAL_EXPR = eINSTANCE.getModalExpr();

		/**
		 * The meta object literal for the '<em><b>Concreteness</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute MODAL_EXPR__CONCRETENESS = eINSTANCE.getModalExpr_Concreteness();

		/**
		 * The meta object literal for the '<em><b>Modality</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute MODAL_EXPR__MODALITY = eINSTANCE.getModalExpr_Modality();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.AssertionImpl <em>Assertion</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.AssertionImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAssertion()
		 * @generated
		 */
		EClass ASSERTION = eINSTANCE.getAssertion();

		/**
		 * The meta object literal for the '<em><b>Default</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute ASSERTION__DEFAULT = eINSTANCE.getAssertion_Default();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.AnnotatedElement <em>Annotated Element</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.AnnotatedElement
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAnnotatedElement()
		 * @generated
		 */
		EClass ANNOTATED_ELEMENT = eINSTANCE.getAnnotatedElement();

		/**
		 * The meta object literal for the '<em><b>Annotations</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ANNOTATED_ELEMENT__ANNOTATIONS = eINSTANCE.getAnnotatedElement_Annotations();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.AnnotationContainerImpl <em>Annotation Container</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.AnnotationContainerImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAnnotationContainer()
		 * @generated
		 */
		EClass ANNOTATION_CONTAINER = eINSTANCE.getAnnotationContainer();

		/**
		 * The meta object literal for the '<em><b>Annotations</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ANNOTATION_CONTAINER__ANNOTATIONS = eINSTANCE.getAnnotationContainer_Annotations();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.AnnotationDeclarationImpl <em>Annotation Declaration</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.AnnotationDeclarationImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAnnotationDeclaration()
		 * @generated
		 */
		EClass ANNOTATION_DECLARATION = eINSTANCE.getAnnotationDeclaration();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.AnnotationImpl <em>Annotation</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.AnnotationImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAnnotation()
		 * @generated
		 */
		EClass ANNOTATION = eINSTANCE.getAnnotation();

		/**
		 * The meta object literal for the '<em><b>Declaration</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ANNOTATION__DECLARATION = eINSTANCE.getAnnotation_Declaration();

		/**
		 * The meta object literal for the '<em><b>Arguments</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ANNOTATION__ARGUMENTS = eINSTANCE.getAnnotation_Arguments();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.AnnotationArgumentImpl <em>Annotation Argument</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.AnnotationArgumentImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getAnnotationArgument()
		 * @generated
		 */
		EClass ANNOTATION_ARGUMENT = eINSTANCE.getAnnotationArgument();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ANNOTATION_ARGUMENT__VALUE = eINSTANCE.getAnnotationArgument_Value();

		/**
		 * The meta object literal for the '<em><b>Parameter</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ANNOTATION_ARGUMENT__PARAMETER = eINSTANCE.getAnnotationArgument_Parameter();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.TopLevelAnnotationImpl <em>Top Level Annotation</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.TopLevelAnnotationImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getTopLevelAnnotation()
		 * @generated
		 */
		EClass TOP_LEVEL_ANNOTATION = eINSTANCE.getTopLevelAnnotation();

		/**
		 * The meta object literal for the '<em><b>Annotation</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference TOP_LEVEL_ANNOTATION__ANNOTATION = eINSTANCE.getTopLevelAnnotation_Annotation();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.OverloadedDeclarationImpl <em>Overloaded Declaration</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.OverloadedDeclarationImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getOverloadedDeclaration()
		 * @generated
		 */
		EClass OVERLOADED_DECLARATION = eINSTANCE.getOverloadedDeclaration();

		/**
		 * The meta object literal for the '<em><b>Shadow</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute OVERLOADED_DECLARATION__SHADOW = eINSTANCE.getOverloadedDeclaration_Shadow();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.impl.TheoryActionImpl <em>Theory Action</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.impl.TheoryActionImpl
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getTheoryAction()
		 * @generated
		 */
		EClass THEORY_ACTION = eINSTANCE.getTheoryAction();

		/**
		 * The meta object literal for the '<em><b>Term</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference THEORY_ACTION__TERM = eINSTANCE.getTheoryAction_Term();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.LogicValue <em>Logic Value</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.LogicValue
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getLogicValue()
		 * @generated
		 */
		EEnum LOGIC_VALUE = eINSTANCE.getLogicValue();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.ComparisonOp <em>Comparison Op</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.ComparisonOp
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getComparisonOp()
		 * @generated
		 */
		EEnum COMPARISON_OP = eINSTANCE.getComparisonOp();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.ReferenceKind <em>Reference Kind</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.ReferenceKind
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getReferenceKind()
		 * @generated
		 */
		EEnum REFERENCE_KIND = eINSTANCE.getReferenceKind();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.UnaryOp <em>Unary Op</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.UnaryOp
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getUnaryOp()
		 * @generated
		 */
		EEnum UNARY_OP = eINSTANCE.getUnaryOp();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.BinaryOp <em>Binary Op</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.BinaryOp
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getBinaryOp()
		 * @generated
		 */
		EEnum BINARY_OP = eINSTANCE.getBinaryOp();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.ModuleKind <em>Module Kind</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.ModuleKind
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getModuleKind()
		 * @generated
		 */
		EEnum MODULE_KIND = eINSTANCE.getModuleKind();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.NodeKind <em>Node Kind</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.NodeKind
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getNodeKind()
		 * @generated
		 */
		EEnum NODE_KIND = eINSTANCE.getNodeKind();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.LatticeBinaryOp <em>Lattice Binary Op</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.LatticeBinaryOp
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getLatticeBinaryOp()
		 * @generated
		 */
		EEnum LATTICE_BINARY_OP = eINSTANCE.getLatticeBinaryOp();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.Modality <em>Modality</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.Modality
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getModality()
		 * @generated
		 */
		EEnum MODALITY = eINSTANCE.getModality();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.Concreteness <em>Concreteness</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.Concreteness
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getConcreteness()
		 * @generated
		 */
		EEnum CONCRETENESS = eINSTANCE.getConcreteness();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.RuleKind <em>Rule Kind</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.RuleKind
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getRuleKind()
		 * @generated
		 */
		EEnum RULE_KIND = eINSTANCE.getRuleKind();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.PredicateKind <em>Predicate Kind</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.PredicateKind
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getPredicateKind()
		 * @generated
		 */
		EEnum PREDICATE_KIND = eINSTANCE.getPredicateKind();

		/**
		 * The meta object literal for the '{@link tools.refinery.language.model.problem.ParameterKind <em>Parameter Kind</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see tools.refinery.language.model.problem.ParameterKind
		 * @see tools.refinery.language.model.problem.impl.ProblemPackageImpl#getParameterKind()
		 * @generated
		 */
		EEnum PARAMETER_KIND = eINSTANCE.getParameterKind();

	}

} //ProblemPackage
