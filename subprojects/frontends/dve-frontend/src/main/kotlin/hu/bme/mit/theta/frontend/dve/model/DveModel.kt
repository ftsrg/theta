/*
 * Kotlin internal representation of DVE (DiVinE Verification Environment) models.
 *
 * Based on the DVE specification language semantics as described in:
 *   - Pavel Šimeček, "DiVinE - Distributed Verification Environment", Master Thesis,
 *     Masaryk University, Faculty of Informatics, 2006 (Chapter 2).
 *   - DiVinE Language Guide (paradise.fi.muni.cz)
 *   - ITS-tools DVE documentation (lip6.github.io)
 *
 * A DVE system consists of:
 *   - Global variable declarations (byte or int, optionally arrays)
 *   - Channel declarations (buffered with capacity, or synchronous with capacity 0)
 *   - Process declarations, each being an extended finite-state automaton with:
 *       - Local variable declarations
 *       - A finite set of control states (one initial, optionally accepting/committed)
 *       - Guarded transitions with effects and optional channel synchronization
 *   - A system composition line (async or sync)
 *   - Optional property process (for LTL model checking)
 *
 * Intended usage: ANTLR parser -> DveModel -> XSTS (Theta framework)
 */

package hu.bme.mit.theta.frontend.dve.model

// ============================================================================
// Types
// ============================================================================

/**
 * DVE supports two primitive types: byte (0..255) and int (32-bit signed integer).
 */
enum class DveVariableType {
  BYTE,
  INT
}

// ============================================================================
// Expressions
// ============================================================================

/**
 * Expressions in DVE, used in guards, effects (right-hand side), and channel data.
 *
 * DVE expressions support C-like arithmetic and logical operators:
 *   Arithmetic: +, -, *, /, %
 *   Comparison: ==, !=, <, <=, >, >=
 *   Logical: &&, ||, !
 *   Bitwise: &, |, ^, ~, <<, >>
 *   Parenthesized grouping
 *   Literals, variable references, array accesses, and process state queries
 */
sealed class DveExpression {

  /** Integer literal constant. */
  data class LiteralExpr(val value: Int) : DveExpression()

  /**
   * Reference to a variable. May be a local variable (unqualified) or a
   * variable of another process (qualified as Process.varName).
   */
  data class VarRefExpr(
    val processName: String? = null,
    val varName: String
  ) : DveExpression()

  /**
   * Array element access: varName[index] or Process.varName[index].
   */
  data class ArrayAccessExpr(
    val processName: String? = null,
    val varName: String,
    val index: DveExpression
  ) : DveExpression()

  /**
   * Process state query: Process.stateName evaluates to non-zero if the
   * process is currently in that state. Used primarily in LTL property
   * definitions and guards.
   */
  data class ProcessStateExpr(
    val processName: String,
    val stateName: String
  ) : DveExpression()

  /** Unary expression: !, -, ~ */
  data class UnaryExpr(
    val op: DveUnaryOp,
    val operand: DveExpression
  ) : DveExpression()

  /** Binary expression for arithmetic, comparison, logical, and bitwise ops. */
  data class BinaryExpr(
    val left: DveExpression,
    val op: DveBinaryOp,
    val right: DveExpression
  ) : DveExpression()
}

enum class DveUnaryOp {
  NOT,        // !
  NEG,        // - (arithmetic negation)
  BITNOT      // ~
}

enum class DveBinaryOp {
  // Arithmetic
  ADD, SUB, MUL, DIV, MOD,
  // Comparison
  EQ, NEQ, LT, LEQ, GT, GEQ,
  // Logical
  AND, OR,
  // Bitwise
  BITAND, BITOR, BITXOR, SHL, SHR
}

// ============================================================================
// Left-hand side of assignments (effects)
// ============================================================================

/**
 * An assignable location: a variable or an array element.
 */
sealed class DveLValue {
  data class VarLValue(
    val processName: String? = null,
    val varName: String
  ) : DveLValue()

  data class ArrayLValue(
    val processName: String? = null,
    val varName: String,
    val index: DveExpression
  ) : DveLValue()
}

// ============================================================================
// Variable declarations
// ============================================================================

/**
 * Declaration of a scalar variable.
 *   e.g., byte x = 0;  or  int counter;
 */
data class DveVariableDecl(
  val name: String,
  val type: DveVariableType,
  val initialValue: DveExpression? = null
)

/**
 * Declaration of a one-dimensional array variable.
 *   e.g., byte flags[4] = {0, 0, 0, 0};
 * DVE only supports 1D arrays. The size must be a compile-time constant.
 */
data class DveArrayDecl(
  val name: String,
  val type: DveVariableType,
  val size: Int,
  val initialValues: List<DveExpression>? = null
)

/**
 * A variable declaration is either a scalar or an array.
 */
sealed class DveVarOrArrayDecl {
  data class Scalar(val decl: DveVariableDecl) : DveVarOrArrayDecl()
  data class Array(val decl: DveArrayDecl) : DveVarOrArrayDecl()
}

// ============================================================================
// Channels
// ============================================================================

/**
 * DVE channel declaration.
 *
 * Channels are used for synchronization between exactly two processes.
 *   - A channel with bufferSize == 0 is synchronous (rendezvous):
 *     the sender and receiver must synchronize simultaneously.
 *   - A channel with bufferSize > 0 is buffered (asynchronous FIFO):
 *     messages are queued up to the buffer capacity.
 *
 * Channels can optionally carry typed data items per message.
 *
 * Syntax: channel ch {byte, int} [3];
 *   -> buffered channel 'ch' carrying a (byte, int) tuple, capacity 3.
 * Syntax: channel sync_ch {0};
 *   -> synchronous channel 'sync_ch' with no data.
 * Syntax: channel data_ch {byte} [0];
 *   -> synchronous channel carrying one byte.
 */
data class DveChannelDecl(
  val name: String,
  val typedFields: List<DveVariableType> = emptyList(),
  val bufferSize: Int = 0
)

// ============================================================================
// Synchronization actions on transitions
// ============================================================================

/**
 * A synchronization action on a transition. Exactly two processes can
 * synchronize in one step on the same channel: one performs a send (!)
 * and the other a receive (?).
 *
 * Syntax in transitions:
 *   sync ch!expr1,expr2;    (send values)
 *   sync ch?var1,var2;      (receive into variables)
 *   sync ch!;               (send with no data, just synchronize)
 *   sync ch?;               (receive with no data, just synchronize)
 */
sealed class DveSyncAction {
  data class Send(
    val channelName: String,
    val values: List<DveExpression> = emptyList()
  ) : DveSyncAction()

  data class Receive(
    val channelName: String,
    val variables: List<DveLValue> = emptyList()
  ) : DveSyncAction()
}

// ============================================================================
// Transitions
// ============================================================================

/**
 * An assignment effect: lvalue = rvalue.
 * Effects are executed when a transition fires.
 */
data class DveAssignment(
  val lvalue: DveLValue,
  val rvalue: DveExpression
)

/**
 * A transition in a DVE process.
 *
 * Syntax:
 *   sourceState -> targetState { guard expr; sync ch!val; effect x = 1, y = 2; }
 *
 * All clauses (guard, sync, effect) are optional.
 * A transition is enabled when:
 *   1. The process is in sourceState
 *   2. The guard expression evaluates to non-zero (if present)
 *   3. Channel synchronization constraints are met (if sync is present)
 *   4. If sourceState is committed, this transition has priority over
 *      non-committed transitions in the system
 *
 * When fired:
 *   1. The sync action is performed (send/receive data)
 *   2. The effect assignments are executed in order
 *   3. The process moves to targetState
 *
 * Note: Two processes synchronizing on a channel must not assign
 * to the same variable — this is a modelling error.
 */
data class DveTransition(
  val sourceState: String,
  val targetState: String,
  val guard: DveExpression? = null,
  val sync: DveSyncAction? = null,
  val effects: List<DveAssignment> = emptyList()
)

// ============================================================================
// Assertions
// ============================================================================

/**
 * An assertion associates a boolean expression with a process state.
 * The expression must evaluate to non-zero whenever the process is in that state.
 *
 * Syntax: assert stateName: expr, stateName2: expr2;
 */
data class DveAssertion(
  val stateName: String,
  val expression: DveExpression
)

// ============================================================================
// Process
// ============================================================================

/**
 * A DVE process: an extended finite-state automaton.
 *
 * Each process has:
 *   - A name (unique identifier)
 *   - Local variable declarations
 *   - A set of named control states, with one designated initial state
 *   - Optionally, some accepting states (for LTL property automata)
 *   - Optionally, some committed states (for modelling atomic actions)
 *   - Assertions mapping states to invariant expressions
 *   - A list of transitions between states
 *
 * Committed states semantics:
 *   When any process in the system is in a committed state, ONLY transitions
 *   originating from committed states (in any process) may fire. This models
 *   atomic sequences of transitions.
 *
 * Accepting states semantics:
 *   Used for property processes (Büchi automata). An accepting cycle in the
 *   product automaton indicates a counterexample to the verified LTL property.
 */
data class DveProcess(
  val name: String,
  val variables: List<DveVarOrArrayDecl> = emptyList(),
  val states: List<String>,
  val initialState: String,
  val acceptingStates: List<String> = emptyList(),
  val committedStates: List<String> = emptyList(),
  val assertions: List<DveAssertion> = emptyList(),
  val transitions: List<DveTransition> = emptyList()
)

// ============================================================================
// System composition
// ============================================================================

/**
 * DVE system composition mode.
 *
 * In asynchronous composition (the common case), processes interleave:
 * at each step, one process (or a synchronizing pair) executes a transition.
 *
 * In synchronous composition, all processes take a step simultaneously
 * (less commonly used; not well supported in later tool versions).
 *
 * Syntax (last line of DVE source):
 *   system async;
 *   system sync;
 *
 * An optional property process can be specified:
 *   system async property prop_process;
 */
enum class DveSystemType {
  ASYNC,
  SYNC
}

data class DveSystemDecl(
  val type: DveSystemType,
  val propertyProcessName: String? = null
)

// ============================================================================
// Top-level model
// ============================================================================

/**
 * A complete DVE model.
 *
 * Structure of a DVE source file (order matters):
 *   1. Global variable declarations (byte/int, scalars or arrays)
 *   2. Channel declarations
 *   3. Process declarations (each containing local vars, states, transitions)
 *   4. System composition line
 *
 * Namespace rules:
 *   There is a single common namespace for channels, variables, processes, and
 *   states. Identifiers must be unique within their scope. When a variable A is
 *   declared in process P1, there cannot be a variable A, a state A in that
 *   process, a global variable A, a channel A, or a process A. The same local
 *   variable name may appear in a *different* process.
 *
 * Semantics:
 *   The system induces a labeled transition system (LTS) where:
 *   - A global state = (process_states, global_vars, local_vars, channel_buffers)
 *   - The initial state: all processes in their initial state, all variables
 *     at their initial values (default 0 if unspecified), all channels empty.
 *   - Enabled transitions are determined by the composition mode:
 *       async: one process (or one synchronizing pair) steps per global transition
 *       sync: all processes step simultaneously
 *   - Committed state priority: if any process is in a committed state,
 *     only transitions from committed states may fire.
 */
data class DveModel(
  val globalVariables: List<DveVarOrArrayDecl> = emptyList(),
  val channels: List<DveChannelDecl> = emptyList(),
  val processes: List<DveProcess> = emptyList(),
  val system: DveSystemDecl
)