/**
 */
package tools.refinery.language.model.problem;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.eclipse.emf.common.util.Enumerator;

/**
 * <!-- begin-user-doc -->
 * A representation of the literals of the enumeration '<em><b>Lattice Binary Op</b></em>',
 * and utility methods for working with them.
 * <!-- end-user-doc -->
 * @see tools.refinery.language.model.problem.ProblemPackage#getLatticeBinaryOp()
 * @model
 * @generated
 */
public enum LatticeBinaryOp implements Enumerator
{
	/**
	 * The '<em><b>MEET</b></em>' literal object.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #MEET_VALUE
	 * @generated
	 * @ordered
	 */
	MEET(0, "MEET", "MEET"),

	/**
	 * The '<em><b>JOIN</b></em>' literal object.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #JOIN_VALUE
	 * @generated
	 * @ordered
	 */
	JOIN(1, "JOIN", "JOIN"),

	/**
	 * The '<em><b>EQ</b></em>' literal object.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #EQ_VALUE
	 * @generated
	 * @ordered
	 */
	EQ(2, "EQ", "EQ"),

	/**
	 * The '<em><b>NOT EQ</b></em>' literal object.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #NOT_EQ_VALUE
	 * @generated
	 * @ordered
	 */
	NOT_EQ(3, "NOT_EQ", "NOT_EQ"),

	/**
	 * The '<em><b>SUBSET</b></em>' literal object.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #SUBSET_VALUE
	 * @generated
	 * @ordered
	 */
	SUBSET(5, "SUBSET", "SUBSET"),

	/**
	 * The '<em><b>SUPERSET</b></em>' literal object.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #SUPERSET_VALUE
	 * @generated
	 * @ordered
	 */
	SUPERSET(6, "SUPERSET", "SUPERSET");

	/**
	 * The '<em><b>MEET</b></em>' literal value.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #MEET
	 * @model
	 * @generated
	 * @ordered
	 */
	public static final int MEET_VALUE = 0;

	/**
	 * The '<em><b>JOIN</b></em>' literal value.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #JOIN
	 * @model
	 * @generated
	 * @ordered
	 */
	public static final int JOIN_VALUE = 1;

	/**
	 * The '<em><b>EQ</b></em>' literal value.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #EQ
	 * @model
	 * @generated
	 * @ordered
	 */
	public static final int EQ_VALUE = 2;

	/**
	 * The '<em><b>NOT EQ</b></em>' literal value.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #NOT_EQ
	 * @model
	 * @generated
	 * @ordered
	 */
	public static final int NOT_EQ_VALUE = 3;

	/**
	 * The '<em><b>SUBSET</b></em>' literal value.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #SUBSET
	 * @model
	 * @generated
	 * @ordered
	 */
	public static final int SUBSET_VALUE = 5;

	/**
	 * The '<em><b>SUPERSET</b></em>' literal value.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #SUPERSET
	 * @model
	 * @generated
	 * @ordered
	 */
	public static final int SUPERSET_VALUE = 6;

	/**
	 * An array of all the '<em><b>Lattice Binary Op</b></em>' enumerators.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private static final LatticeBinaryOp[] VALUES_ARRAY =
		new LatticeBinaryOp[]
		{
			MEET,
			JOIN,
			EQ,
			NOT_EQ,
			SUBSET,
			SUPERSET,
		};

	/**
	 * A public read-only list of all the '<em><b>Lattice Binary Op</b></em>' enumerators.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static final List<LatticeBinaryOp> VALUES = Collections.unmodifiableList(Arrays.asList(VALUES_ARRAY));

	/**
	 * Returns the '<em><b>Lattice Binary Op</b></em>' literal with the specified literal value.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param literal the literal.
	 * @return the matching enumerator or <code>null</code>.
	 * @generated
	 */
	public static LatticeBinaryOp get(String literal)
	{
		for (int i = 0; i < VALUES_ARRAY.length; ++i)
		{
			LatticeBinaryOp result = VALUES_ARRAY[i];
			if (result.toString().equals(literal))
			{
				return result;
			}
		}
		return null;
	}

	/**
	 * Returns the '<em><b>Lattice Binary Op</b></em>' literal with the specified name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param name the name.
	 * @return the matching enumerator or <code>null</code>.
	 * @generated
	 */
	public static LatticeBinaryOp getByName(String name)
	{
		for (int i = 0; i < VALUES_ARRAY.length; ++i)
		{
			LatticeBinaryOp result = VALUES_ARRAY[i];
			if (result.getName().equals(name))
			{
				return result;
			}
		}
		return null;
	}

	/**
	 * Returns the '<em><b>Lattice Binary Op</b></em>' literal with the specified integer value.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the integer value.
	 * @return the matching enumerator or <code>null</code>.
	 * @generated
	 */
	public static LatticeBinaryOp get(int value)
	{
		switch (value)
		{
			case MEET_VALUE: return MEET;
			case JOIN_VALUE: return JOIN;
			case EQ_VALUE: return EQ;
			case NOT_EQ_VALUE: return NOT_EQ;
			case SUBSET_VALUE: return SUBSET;
			case SUPERSET_VALUE: return SUPERSET;
		}
		return null;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private final int value;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private final String name;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private final String literal;

	/**
	 * Only this class can construct instances.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private LatticeBinaryOp(int value, String name, String literal)
	{
		this.value = value;
		this.name = name;
		this.literal = literal;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public int getValue()
	{
	  return value;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String getName()
	{
	  return name;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String getLiteral()
	{
	  return literal;
	}

	/**
	 * Returns the literal value of the enumerator, which is its string representation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public String toString()
	{
		return literal;
	}
	
} //LatticeBinaryOp
