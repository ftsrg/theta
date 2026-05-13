/**
 */
package tools.refinery.language.model.problem.util;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;

import org.eclipse.emf.ecore.util.Switch;

import tools.refinery.language.model.problem.*;

/**
 * <!-- begin-user-doc -->
 * The <b>Switch</b> for the model's inheritance hierarchy.
 * It supports the call {@link #doSwitch(EObject) doSwitch(object)}
 * to invoke the <code>caseXXX</code> method for each class of the model,
 * starting with the actual class of the object
 * and proceeding up the inheritance hierarchy
 * until a non-null result is returned,
 * which is the result of the switch.
 * <!-- end-user-doc -->
 * @see tools.refinery.language.model.problem.ProblemPackage
 * @generated
 */
public class ProblemSwitch<T> extends Switch<T>
{
	/**
	 * The cached model package
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected static ProblemPackage modelPackage;

	/**
	 * Creates an instance of the switch.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ProblemSwitch()
	{
		if (modelPackage == null)
		{
			modelPackage = ProblemPackage.eINSTANCE;
		}
	}

	/**
	 * Checks whether this is a switch for the given package.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param ePackage the package in question.
	 * @return whether this is a switch for the given package.
	 * @generated
	 */
	@Override
	protected boolean isSwitchFor(EPackage ePackage)
	{
		return ePackage == modelPackage;
	}

	/**
	 * Calls <code>caseXXX</code> for each class of the model until one returns a non null result; it yields that result.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the first non-null result returned by a <code>caseXXX</code> call.
	 * @generated
	 */
	@Override
	protected T doSwitch(int classifierID, EObject theEObject)
	{
		switch (classifierID)
		{
			case ProblemPackage.PROBLEM:
			{
				Problem problem = (Problem)theEObject;
				T result = caseProblem(problem);
				if (result == null) result = caseNamedElement(problem);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.CLASS_DECLARATION:
			{
				ClassDeclaration classDeclaration = (ClassDeclaration)theEObject;
				T result = caseClassDeclaration(classDeclaration);
				if (result == null) result = caseStatement(classDeclaration);
				if (result == null) result = caseRelation(classDeclaration);
				if (result == null) result = caseAnnotatedElement(classDeclaration);
				if (result == null) result = caseNamedElement(classDeclaration);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.REFERENCE_DECLARATION:
			{
				ReferenceDeclaration referenceDeclaration = (ReferenceDeclaration)theEObject;
				T result = caseReferenceDeclaration(referenceDeclaration);
				if (result == null) result = caseRelation(referenceDeclaration);
				if (result == null) result = caseAnnotatedElement(referenceDeclaration);
				if (result == null) result = caseNamedElement(referenceDeclaration);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.NAMED_ELEMENT:
			{
				NamedElement namedElement = (NamedElement)theEObject;
				T result = caseNamedElement(namedElement);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.PREDICATE_DEFINITION:
			{
				PredicateDefinition predicateDefinition = (PredicateDefinition)theEObject;
				T result = casePredicateDefinition(predicateDefinition);
				if (result == null) result = caseParametricDefinition(predicateDefinition);
				if (result == null) result = caseRelation(predicateDefinition);
				if (result == null) result = caseStatement(predicateDefinition);
				if (result == null) result = caseAnnotatedElement(predicateDefinition);
				if (result == null) result = caseNamedElement(predicateDefinition);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.PARAMETER:
			{
				Parameter parameter = (Parameter)theEObject;
				T result = caseParameter(parameter);
				if (result == null) result = caseVariable(parameter);
				if (result == null) result = caseAnnotatedElement(parameter);
				if (result == null) result = caseVariableOrNode(parameter);
				if (result == null) result = caseNamedElement(parameter);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.VARIABLE:
			{
				Variable variable = (Variable)theEObject;
				T result = caseVariable(variable);
				if (result == null) result = caseVariableOrNode(variable);
				if (result == null) result = caseNamedElement(variable);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.ATOM:
			{
				Atom atom = (Atom)theEObject;
				T result = caseAtom(atom);
				if (result == null) result = caseExpr(atom);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.IMPLICIT_VARIABLE:
			{
				ImplicitVariable implicitVariable = (ImplicitVariable)theEObject;
				T result = caseImplicitVariable(implicitVariable);
				if (result == null) result = caseVariable(implicitVariable);
				if (result == null) result = caseVariableOrNode(implicitVariable);
				if (result == null) result = caseNamedElement(implicitVariable);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.EXISTENTIAL_QUANTIFIER:
			{
				ExistentialQuantifier existentialQuantifier = (ExistentialQuantifier)theEObject;
				T result = caseExistentialQuantifier(existentialQuantifier);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.ABSTRACT_ASSERTION:
			{
				AbstractAssertion abstractAssertion = (AbstractAssertion)theEObject;
				T result = caseAbstractAssertion(abstractAssertion);
				if (result == null) result = caseExistentialQuantifier(abstractAssertion);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.NODE:
			{
				Node node = (Node)theEObject;
				T result = caseNode(node);
				if (result == null) result = caseVariableOrNode(node);
				if (result == null) result = caseAnnotatedElement(node);
				if (result == null) result = caseNamedElement(node);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.SCOPE_DECLARATION:
			{
				ScopeDeclaration scopeDeclaration = (ScopeDeclaration)theEObject;
				T result = caseScopeDeclaration(scopeDeclaration);
				if (result == null) result = caseStatement(scopeDeclaration);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.STATEMENT:
			{
				Statement statement = (Statement)theEObject;
				T result = caseStatement(statement);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.TYPE_SCOPE:
			{
				TypeScope typeScope = (TypeScope)theEObject;
				T result = caseTypeScope(typeScope);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.MULTIPLICITY:
			{
				Multiplicity multiplicity = (Multiplicity)theEObject;
				T result = caseMultiplicity(multiplicity);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.RANGE_MULTIPLICITY:
			{
				RangeMultiplicity rangeMultiplicity = (RangeMultiplicity)theEObject;
				T result = caseRangeMultiplicity(rangeMultiplicity);
				if (result == null) result = caseMultiplicity(rangeMultiplicity);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.EXACT_MULTIPLICITY:
			{
				ExactMultiplicity exactMultiplicity = (ExactMultiplicity)theEObject;
				T result = caseExactMultiplicity(exactMultiplicity);
				if (result == null) result = caseMultiplicity(exactMultiplicity);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.UNBOUNDED_MULTIPLICITY:
			{
				UnboundedMultiplicity unboundedMultiplicity = (UnboundedMultiplicity)theEObject;
				T result = caseUnboundedMultiplicity(unboundedMultiplicity);
				if (result == null) result = caseMultiplicity(unboundedMultiplicity);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.ENUM_DECLARATION:
			{
				EnumDeclaration enumDeclaration = (EnumDeclaration)theEObject;
				T result = caseEnumDeclaration(enumDeclaration);
				if (result == null) result = caseStatement(enumDeclaration);
				if (result == null) result = caseRelation(enumDeclaration);
				if (result == null) result = caseAnnotatedElement(enumDeclaration);
				if (result == null) result = caseNamedElement(enumDeclaration);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.VARIABLE_OR_NODE:
			{
				VariableOrNode variableOrNode = (VariableOrNode)theEObject;
				T result = caseVariableOrNode(variableOrNode);
				if (result == null) result = caseNamedElement(variableOrNode);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.CONSTANT:
			{
				Constant constant = (Constant)theEObject;
				T result = caseConstant(constant);
				if (result == null) result = caseExpr(constant);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.INT_CONSTANT:
			{
				IntConstant intConstant = (IntConstant)theEObject;
				T result = caseIntConstant(intConstant);
				if (result == null) result = caseConstant(intConstant);
				if (result == null) result = caseExpr(intConstant);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.REAL_CONSTANT:
			{
				RealConstant realConstant = (RealConstant)theEObject;
				T result = caseRealConstant(realConstant);
				if (result == null) result = caseConstant(realConstant);
				if (result == null) result = caseExpr(realConstant);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.STRING_CONSTANT:
			{
				StringConstant stringConstant = (StringConstant)theEObject;
				T result = caseStringConstant(stringConstant);
				if (result == null) result = caseConstant(stringConstant);
				if (result == null) result = caseExpr(stringConstant);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.NODE_ASSERTION_ARGUMENT:
			{
				NodeAssertionArgument nodeAssertionArgument = (NodeAssertionArgument)theEObject;
				T result = caseNodeAssertionArgument(nodeAssertionArgument);
				if (result == null) result = caseAssertionArgument(nodeAssertionArgument);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.ASSERTION_ARGUMENT:
			{
				AssertionArgument assertionArgument = (AssertionArgument)theEObject;
				T result = caseAssertionArgument(assertionArgument);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.NODE_DECLARATION:
			{
				NodeDeclaration nodeDeclaration = (NodeDeclaration)theEObject;
				T result = caseNodeDeclaration(nodeDeclaration);
				if (result == null) result = caseStatement(nodeDeclaration);
				if (result == null) result = caseAnnotatedElement(nodeDeclaration);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.WILDCARD_ASSERTION_ARGUMENT:
			{
				WildcardAssertionArgument wildcardAssertionArgument = (WildcardAssertionArgument)theEObject;
				T result = caseWildcardAssertionArgument(wildcardAssertionArgument);
				if (result == null) result = caseAssertionArgument(wildcardAssertionArgument);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.PARAMETRIC_DEFINITION:
			{
				ParametricDefinition parametricDefinition = (ParametricDefinition)theEObject;
				T result = caseParametricDefinition(parametricDefinition);
				if (result == null) result = caseStatement(parametricDefinition);
				if (result == null) result = caseAnnotatedElement(parametricDefinition);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.RULE_DEFINITION:
			{
				RuleDefinition ruleDefinition = (RuleDefinition)theEObject;
				T result = caseRuleDefinition(ruleDefinition);
				if (result == null) result = caseParametricDefinition(ruleDefinition);
				if (result == null) result = caseNamedElement(ruleDefinition);
				if (result == null) result = caseStatement(ruleDefinition);
				if (result == null) result = caseAnnotatedElement(ruleDefinition);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.CONSEQUENT:
			{
				Consequent consequent = (Consequent)theEObject;
				T result = caseConsequent(consequent);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.ACTION:
			{
				Action action = (Action)theEObject;
				T result = caseAction(action);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.ASSERTION_ACTION:
			{
				AssertionAction assertionAction = (AssertionAction)theEObject;
				T result = caseAssertionAction(assertionAction);
				if (result == null) result = caseAction(assertionAction);
				if (result == null) result = caseAbstractAssertion(assertionAction);
				if (result == null) result = caseExistentialQuantifier(assertionAction);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.EXPR:
			{
				Expr expr = (Expr)theEObject;
				T result = caseExpr(expr);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.VARIABLE_OR_NODE_EXPR:
			{
				VariableOrNodeExpr variableOrNodeExpr = (VariableOrNodeExpr)theEObject;
				T result = caseVariableOrNodeExpr(variableOrNodeExpr);
				if (result == null) result = caseExpr(variableOrNodeExpr);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.BINARY_EXPR:
			{
				BinaryExpr binaryExpr = (BinaryExpr)theEObject;
				T result = caseBinaryExpr(binaryExpr);
				if (result == null) result = caseExpr(binaryExpr);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.UNARY_EXPR:
			{
				UnaryExpr unaryExpr = (UnaryExpr)theEObject;
				T result = caseUnaryExpr(unaryExpr);
				if (result == null) result = caseExpr(unaryExpr);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.ARITHMETIC_UNARY_EXPR:
			{
				ArithmeticUnaryExpr arithmeticUnaryExpr = (ArithmeticUnaryExpr)theEObject;
				T result = caseArithmeticUnaryExpr(arithmeticUnaryExpr);
				if (result == null) result = caseUnaryExpr(arithmeticUnaryExpr);
				if (result == null) result = caseExpr(arithmeticUnaryExpr);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.AGGREGATION_EXPR:
			{
				AggregationExpr aggregationExpr = (AggregationExpr)theEObject;
				T result = caseAggregationExpr(aggregationExpr);
				if (result == null) result = caseExpr(aggregationExpr);
				if (result == null) result = caseExistentialQuantifier(aggregationExpr);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.COMPARISON_EXPR:
			{
				ComparisonExpr comparisonExpr = (ComparisonExpr)theEObject;
				T result = caseComparisonExpr(comparisonExpr);
				if (result == null) result = caseBinaryExpr(comparisonExpr);
				if (result == null) result = caseExpr(comparisonExpr);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.NEGATION_EXPR:
			{
				NegationExpr negationExpr = (NegationExpr)theEObject;
				T result = caseNegationExpr(negationExpr);
				if (result == null) result = caseExistentialQuantifier(negationExpr);
				if (result == null) result = caseUnaryExpr(negationExpr);
				if (result == null) result = caseExpr(negationExpr);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.FUNCTION_DEFINITION:
			{
				FunctionDefinition functionDefinition = (FunctionDefinition)theEObject;
				T result = caseFunctionDefinition(functionDefinition);
				if (result == null) result = caseParametricDefinition(functionDefinition);
				if (result == null) result = caseRelation(functionDefinition);
				if (result == null) result = caseStatement(functionDefinition);
				if (result == null) result = caseAnnotatedElement(functionDefinition);
				if (result == null) result = caseNamedElement(functionDefinition);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.CONJUNCTION:
			{
				Conjunction conjunction = (Conjunction)theEObject;
				T result = caseConjunction(conjunction);
				if (result == null) result = caseExistentialQuantifier(conjunction);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.CASE:
			{
				Case case_ = (Case)theEObject;
				T result = caseCase(case_);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.ARITHMETIC_BINARY_EXPR:
			{
				ArithmeticBinaryExpr arithmeticBinaryExpr = (ArithmeticBinaryExpr)theEObject;
				T result = caseArithmeticBinaryExpr(arithmeticBinaryExpr);
				if (result == null) result = caseBinaryExpr(arithmeticBinaryExpr);
				if (result == null) result = caseExpr(arithmeticBinaryExpr);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.RELATION:
			{
				Relation relation = (Relation)theEObject;
				T result = caseRelation(relation);
				if (result == null) result = caseNamedElement(relation);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.RANGE_EXPR:
			{
				RangeExpr rangeExpr = (RangeExpr)theEObject;
				T result = caseRangeExpr(rangeExpr);
				if (result == null) result = caseBinaryExpr(rangeExpr);
				if (result == null) result = caseExpr(rangeExpr);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.LOGIC_CONSTANT:
			{
				LogicConstant logicConstant = (LogicConstant)theEObject;
				T result = caseLogicConstant(logicConstant);
				if (result == null) result = caseConstant(logicConstant);
				if (result == null) result = caseExpr(logicConstant);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.IMPORT_STATEMENT:
			{
				ImportStatement importStatement = (ImportStatement)theEObject;
				T result = caseImportStatement(importStatement);
				if (result == null) result = caseStatement(importStatement);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.DATATYPE_DECLARATION:
			{
				DatatypeDeclaration datatypeDeclaration = (DatatypeDeclaration)theEObject;
				T result = caseDatatypeDeclaration(datatypeDeclaration);
				if (result == null) result = caseRelation(datatypeDeclaration);
				if (result == null) result = caseStatement(datatypeDeclaration);
				if (result == null) result = caseAnnotatedElement(datatypeDeclaration);
				if (result == null) result = caseNamedElement(datatypeDeclaration);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.LATTICE_BINARY_EXPR:
			{
				LatticeBinaryExpr latticeBinaryExpr = (LatticeBinaryExpr)theEObject;
				T result = caseLatticeBinaryExpr(latticeBinaryExpr);
				if (result == null) result = caseBinaryExpr(latticeBinaryExpr);
				if (result == null) result = caseExpr(latticeBinaryExpr);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.ASSIGNMENT_EXPR:
			{
				AssignmentExpr assignmentExpr = (AssignmentExpr)theEObject;
				T result = caseAssignmentExpr(assignmentExpr);
				if (result == null) result = caseBinaryExpr(assignmentExpr);
				if (result == null) result = caseExpr(assignmentExpr);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.INFINITE_CONSTANT:
			{
				InfiniteConstant infiniteConstant = (InfiniteConstant)theEObject;
				T result = caseInfiniteConstant(infiniteConstant);
				if (result == null) result = caseConstant(infiniteConstant);
				if (result == null) result = caseExpr(infiniteConstant);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.AGGREGATOR_DECLARATION:
			{
				AggregatorDeclaration aggregatorDeclaration = (AggregatorDeclaration)theEObject;
				T result = caseAggregatorDeclaration(aggregatorDeclaration);
				if (result == null) result = caseStatement(aggregatorDeclaration);
				if (result == null) result = caseNamedElement(aggregatorDeclaration);
				if (result == null) result = caseAnnotatedElement(aggregatorDeclaration);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.MODAL_EXPR:
			{
				ModalExpr modalExpr = (ModalExpr)theEObject;
				T result = caseModalExpr(modalExpr);
				if (result == null) result = caseUnaryExpr(modalExpr);
				if (result == null) result = caseExpr(modalExpr);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.ASSERTION:
			{
				Assertion assertion = (Assertion)theEObject;
				T result = caseAssertion(assertion);
				if (result == null) result = caseStatement(assertion);
				if (result == null) result = caseAbstractAssertion(assertion);
				if (result == null) result = caseExistentialQuantifier(assertion);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.ANNOTATED_ELEMENT:
			{
				AnnotatedElement annotatedElement = (AnnotatedElement)theEObject;
				T result = caseAnnotatedElement(annotatedElement);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.ANNOTATION_CONTAINER:
			{
				AnnotationContainer annotationContainer = (AnnotationContainer)theEObject;
				T result = caseAnnotationContainer(annotationContainer);
				if (result == null) result = caseStatement(annotationContainer);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.ANNOTATION_DECLARATION:
			{
				AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)theEObject;
				T result = caseAnnotationDeclaration(annotationDeclaration);
				if (result == null) result = caseParametricDefinition(annotationDeclaration);
				if (result == null) result = caseNamedElement(annotationDeclaration);
				if (result == null) result = caseStatement(annotationDeclaration);
				if (result == null) result = caseAnnotatedElement(annotationDeclaration);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.ANNOTATION:
			{
				Annotation annotation = (Annotation)theEObject;
				T result = caseAnnotation(annotation);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.ANNOTATION_ARGUMENT:
			{
				AnnotationArgument annotationArgument = (AnnotationArgument)theEObject;
				T result = caseAnnotationArgument(annotationArgument);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.TOP_LEVEL_ANNOTATION:
			{
				TopLevelAnnotation topLevelAnnotation = (TopLevelAnnotation)theEObject;
				T result = caseTopLevelAnnotation(topLevelAnnotation);
				if (result == null) result = caseStatement(topLevelAnnotation);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.OVERLOADED_DECLARATION:
			{
				OverloadedDeclaration overloadedDeclaration = (OverloadedDeclaration)theEObject;
				T result = caseOverloadedDeclaration(overloadedDeclaration);
				if (result == null) result = caseParametricDefinition(overloadedDeclaration);
				if (result == null) result = caseRelation(overloadedDeclaration);
				if (result == null) result = caseStatement(overloadedDeclaration);
				if (result == null) result = caseAnnotatedElement(overloadedDeclaration);
				if (result == null) result = caseNamedElement(overloadedDeclaration);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case ProblemPackage.THEORY_ACTION:
			{
				TheoryAction theoryAction = (TheoryAction)theEObject;
				T result = caseTheoryAction(theoryAction);
				if (result == null) result = caseAction(theoryAction);
				if (result == null) result = caseExistentialQuantifier(theoryAction);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			default: return defaultCase(theEObject);
		}
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Problem</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Problem</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseProblem(Problem object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Class Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Class Declaration</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseClassDeclaration(ClassDeclaration object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Reference Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Reference Declaration</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseReferenceDeclaration(ReferenceDeclaration object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Named Element</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Named Element</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseNamedElement(NamedElement object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Predicate Definition</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Predicate Definition</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T casePredicateDefinition(PredicateDefinition object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Parameter</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Parameter</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseParameter(Parameter object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Variable</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Variable</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseVariable(Variable object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Atom</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Atom</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseAtom(Atom object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Implicit Variable</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Implicit Variable</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseImplicitVariable(ImplicitVariable object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Existential Quantifier</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Existential Quantifier</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseExistentialQuantifier(ExistentialQuantifier object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Abstract Assertion</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Abstract Assertion</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseAbstractAssertion(AbstractAssertion object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Node</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Node</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseNode(Node object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Scope Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Scope Declaration</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseScopeDeclaration(ScopeDeclaration object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Statement</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Statement</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseStatement(Statement object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Type Scope</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Type Scope</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseTypeScope(TypeScope object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Multiplicity</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Multiplicity</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseMultiplicity(Multiplicity object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Range Multiplicity</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Range Multiplicity</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseRangeMultiplicity(RangeMultiplicity object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Exact Multiplicity</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Exact Multiplicity</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseExactMultiplicity(ExactMultiplicity object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Unbounded Multiplicity</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Unbounded Multiplicity</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseUnboundedMultiplicity(UnboundedMultiplicity object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Enum Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Enum Declaration</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseEnumDeclaration(EnumDeclaration object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Variable Or Node</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Variable Or Node</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseVariableOrNode(VariableOrNode object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Constant</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Constant</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseConstant(Constant object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Int Constant</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Int Constant</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseIntConstant(IntConstant object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Real Constant</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Real Constant</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseRealConstant(RealConstant object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>String Constant</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>String Constant</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseStringConstant(StringConstant object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Node Assertion Argument</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Node Assertion Argument</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseNodeAssertionArgument(NodeAssertionArgument object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Assertion Argument</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Assertion Argument</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseAssertionArgument(AssertionArgument object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Node Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Node Declaration</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseNodeDeclaration(NodeDeclaration object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Wildcard Assertion Argument</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Wildcard Assertion Argument</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseWildcardAssertionArgument(WildcardAssertionArgument object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Parametric Definition</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Parametric Definition</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseParametricDefinition(ParametricDefinition object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Rule Definition</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Rule Definition</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseRuleDefinition(RuleDefinition object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Consequent</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Consequent</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseConsequent(Consequent object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Action</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Action</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseAction(Action object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Assertion Action</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Assertion Action</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseAssertionAction(AssertionAction object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Expr</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Expr</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseExpr(Expr object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Variable Or Node Expr</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Variable Or Node Expr</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseVariableOrNodeExpr(VariableOrNodeExpr object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Binary Expr</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Binary Expr</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseBinaryExpr(BinaryExpr object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Unary Expr</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Unary Expr</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseUnaryExpr(UnaryExpr object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Arithmetic Unary Expr</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Arithmetic Unary Expr</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseArithmeticUnaryExpr(ArithmeticUnaryExpr object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Aggregation Expr</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Aggregation Expr</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseAggregationExpr(AggregationExpr object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Comparison Expr</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Comparison Expr</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseComparisonExpr(ComparisonExpr object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Negation Expr</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Negation Expr</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseNegationExpr(NegationExpr object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Function Definition</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Function Definition</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseFunctionDefinition(FunctionDefinition object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Conjunction</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Conjunction</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseConjunction(Conjunction object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Case</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Case</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseCase(Case object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Arithmetic Binary Expr</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Arithmetic Binary Expr</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseArithmeticBinaryExpr(ArithmeticBinaryExpr object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Relation</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Relation</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseRelation(Relation object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Range Expr</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Range Expr</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseRangeExpr(RangeExpr object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Logic Constant</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Logic Constant</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseLogicConstant(LogicConstant object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Import Statement</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Import Statement</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseImportStatement(ImportStatement object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Datatype Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Datatype Declaration</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseDatatypeDeclaration(DatatypeDeclaration object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Lattice Binary Expr</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Lattice Binary Expr</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseLatticeBinaryExpr(LatticeBinaryExpr object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Assignment Expr</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Assignment Expr</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseAssignmentExpr(AssignmentExpr object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Infinite Constant</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Infinite Constant</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseInfiniteConstant(InfiniteConstant object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Aggregator Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Aggregator Declaration</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseAggregatorDeclaration(AggregatorDeclaration object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Modal Expr</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Modal Expr</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseModalExpr(ModalExpr object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Assertion</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Assertion</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseAssertion(Assertion object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Annotated Element</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Annotated Element</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseAnnotatedElement(AnnotatedElement object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Annotation Container</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Annotation Container</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseAnnotationContainer(AnnotationContainer object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Annotation Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Annotation Declaration</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseAnnotationDeclaration(AnnotationDeclaration object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Annotation</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Annotation</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseAnnotation(Annotation object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Annotation Argument</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Annotation Argument</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseAnnotationArgument(AnnotationArgument object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Top Level Annotation</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Top Level Annotation</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseTopLevelAnnotation(TopLevelAnnotation object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Overloaded Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Overloaded Declaration</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseOverloadedDeclaration(OverloadedDeclaration object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Theory Action</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Theory Action</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseTheoryAction(TheoryAction object)
	{
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>EObject</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch, but this is the last case anyway.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>EObject</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject)
	 * @generated
	 */
	@Override
	public T defaultCase(EObject object)
	{
		return null;
	}

} //ProblemSwitch
