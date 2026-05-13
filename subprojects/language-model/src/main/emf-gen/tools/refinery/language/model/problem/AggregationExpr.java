/**
 */
package tools.refinery.language.model.problem;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Aggregation Expr</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.AggregationExpr#getValue <em>Value</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.AggregationExpr#getCondition <em>Condition</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.AggregationExpr#getAggregator <em>Aggregator</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getAggregationExpr()
 * @model
 * @generated
 */
public interface AggregationExpr extends Expr, ExistentialQuantifier
{
	/**
	 * Returns the value of the '<em><b>Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Value</em>' containment reference.
	 * @see #setValue(Expr)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getAggregationExpr_Value()
	 * @model containment="true"
	 * @generated
	 */
	Expr getValue();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.AggregationExpr#getValue <em>Value</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Value</em>' containment reference.
	 * @see #getValue()
	 * @generated
	 */
	void setValue(Expr value);

	/**
	 * Returns the value of the '<em><b>Condition</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Condition</em>' containment reference.
	 * @see #setCondition(Expr)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getAggregationExpr_Condition()
	 * @model containment="true"
	 * @generated
	 */
	Expr getCondition();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.AggregationExpr#getCondition <em>Condition</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Condition</em>' containment reference.
	 * @see #getCondition()
	 * @generated
	 */
	void setCondition(Expr value);

	/**
	 * Returns the value of the '<em><b>Aggregator</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Aggregator</em>' reference.
	 * @see #setAggregator(AggregatorDeclaration)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getAggregationExpr_Aggregator()
	 * @model
	 * @generated
	 */
	AggregatorDeclaration getAggregator();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.AggregationExpr#getAggregator <em>Aggregator</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Aggregator</em>' reference.
	 * @see #getAggregator()
	 * @generated
	 */
	void setAggregator(AggregatorDeclaration value);

} // AggregationExpr
