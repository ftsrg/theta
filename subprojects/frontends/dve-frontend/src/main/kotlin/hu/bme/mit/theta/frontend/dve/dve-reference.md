# DVE Language Reference for Implementation

This document contains everything needed to:
1. Write an ANTLR4 grammar that parses `.dve` files
2. Build an ANTLR visitor that constructs the Kotlin `DveModel` IR
3. Transform the `DveModel` into XSTS (eXtended Symbolic Transition System) for the Theta framework

---

## 1. DVE CONCRETE SYNTAX

### 1.1 File structure (order matters)

```
<global_variable_declarations>*
<channel_declarations>*
<process_declarations>+
<system_declaration>
```

### 1.2 Variable declarations

Two types: `byte` (0–255) and `int` (32-bit signed).

```dve
// Scalars
byte x;
byte x = 5;
int counter = 0;

// 1D arrays (size must be integer literal)
byte flags[4];
int arr[3] = {1, 2, 3};
```

Global variables are declared before any process. Local variables are declared at the beginning of a process body.

**Constants cannot be used as array size parameters** — only integer literals.

### 1.3 Channel declarations

```dve
// Synchronous (rendezvous), no data
channel sync_ch {0};

// Synchronous, carrying typed data
channel data_ch {byte} [0];
channel pair_ch {byte, int} [0];

// Buffered (async FIFO), capacity > 0
channel buf_ch {byte} [3];
```

The `{0}` form declares a synchronous channel with no typed fields.
The `{type1, type2, ...} [capacity]` form declares typed fields and buffer size.

### 1.4 Process declarations

```dve
process ProcessName {
    // Local variables (optional)
    byte localVar = 0;
    int arr[2];

    // State declarations (required)
    state s0, s1, s2, critical;
    init s0;

    // Accepting states (optional, for property processes)
    accept s2;

    // Committed states (optional, for atomic sequences)
    commit s1;

    // Assertions (optional)
    assert s0: localVar >= 0, s1: localVar < 10;

    // Transitions (required)
    trans
        s0 -> s1 { guard localVar == 0; effect localVar = 1; },
        s1 -> s2 { guard localVar > 0; sync ch!localVar; effect localVar = 0; },
        s2 -> s0 {};
}
```

**Order within process body**: variables, then `state`, then `init`, then optionally `accept`/`commit`, then optionally `assert`, then `trans`.

### 1.5 Transition syntax

```
sourceState -> targetState { <clauses> }
```

Clauses (all optional, semicolon-terminated within braces):
- `guard <expr>;` — boolean condition for enabling
- `sync <channel>!<expr_list>;` — send on channel
- `sync <channel>?<lvalue_list>;` — receive from channel
- `effect <assignment_list>;` — comma-separated assignments

```dve
// Full example
s0 -> s1 { guard x > 0 && y == 1; sync ch!x,y; effect x = 0, y = y + 1; }

// Minimal (no guard, no sync, no effect)
s0 -> s1 {}

// Sync only (no data)
s0 -> s1 { sync ch!; }
s0 -> s1 { sync ch?; }
```

Multiple transitions are comma-separated after `trans` keyword, terminated with semicolon:
```dve
trans
    s0 -> s1 { guard x == 0; },
    s0 -> s2 { guard x == 1; },
    s1 -> s0 { effect x = 1; };
```

### 1.6 Expressions

C-like expression syntax with these operators (in precedence order, low to high):

| Precedence | Operators | Associativity |
|---|---|---|
| 1 | `\|\|` | left |
| 2 | `&&` | left |
| 3 | `\|` | left |
| 4 | `^` | left |
| 5 | `&` | left |
| 6 | `==` `!=` | left |
| 7 | `<` `<=` `>` `>=` | left |
| 8 | `<<` `>>` | left |
| 9 | `+` `-` | left |
| 10 | `*` `/` `%` | left |
| 11 (unary) | `!` `-` `~` | right (prefix) |
| 12 | `()` `[]` `.` | — |

Atoms:
- Integer literals: `0`, `42`, `255`
- Variable reference: `x`, `ProcessName.x`
- Array access: `arr[expr]`, `ProcessName.arr[expr]`
- Process state test: `ProcessName.stateName` (true iff process is in that state — **syntactically identical to qualified variable reference, must be resolved semantically**)
- Parenthesized: `(expr)`

### 1.7 Assignment targets (LValues)

```
x = expr
arr[expr] = expr
ProcessName.x = expr
ProcessName.arr[expr] = expr
```

Processes can read/write other processes' local variables via qualified names (used in property processes and occasionally in models).

### 1.8 System declaration (last line)

```dve
system async;
system sync;
system async property PropertyProcessName;
system sync property PropertyProcessName;
```

### 1.9 Comments

C-style:
```dve
// line comment
/* block comment */
```

### 1.10 Identifiers

Standard C-like: `[a-zA-Z_][a-zA-Z0-9_]*`

### 1.11 Reserved keywords

```
byte int process state init accept commit assert trans
guard sync effect channel system async sync property
```

---

## 2. DVE SEMANTICS (for XSTS transformation)

### 2.1 Global state

A system state is a tuple:
```
(pc[0], pc[1], ..., pc[n-1],   // process control states (one per process)
 gvar[0], ..., gvar[m-1],       // global variables
 lvar[p][0], ..., lvar[p][k-1], // local variables per process
 chbuf[0], ..., chbuf[c-1])     // channel buffer contents
```

**Initial state**: every process in its `init` state, all variables at their declared initial values (default `0` if no initializer), all channel buffers empty.

### 2.2 Asynchronous composition (the common case)

At each step, **exactly one** of the following happens:
1. **One process** fires an enabled non-synchronizing transition, OR
2. **Exactly two processes** fire simultaneously — one with `sync ch!` and one with `sync ch?` on the same channel

Selection among enabled transitions is **nondeterministic**.

### 2.3 Transition enabling conditions

A transition `s -> t { guard g; sync ...; effect ...; }` in process P is enabled when:
1. P is currently in state `s`
2. Guard `g` evaluates to non-zero (or there is no guard)
3. Sync constraints are satisfied:
   - `sync ch!values`: for synchronous channels (capacity 0), a matching `ch?` transition must be simultaneously enabled in another process. For buffered channels, the buffer must not be full.
   - `sync ch?vars`: for synchronous channels, a matching `ch!` must be simultaneously enabled. For buffered channels, the buffer must not be empty.
   - No sync clause: always satisfiable (local transition)

### 2.4 Committed states priority

**Critical rule**: If ANY process in the system is in a committed state, then ONLY transitions whose source state is a committed state may fire (across ALL processes). This gives committed-state transitions strict priority.

This is used to model atomic multi-step sequences: once a process enters a committed state, it (and any other process in a committed state) must leave the committed state before any non-committed transition can fire.

### 2.5 Synchronous channel (rendezvous) semantics

When channel has capacity 0:
- Send `ch!v1,v2` and receive `ch?x,y` must happen simultaneously
- The values v1,v2 are evaluated in the sender, then assigned to x,y in the receiver
- Both processes' effects are applied (sender first, then receiver)
- Both processes transition to their respective target states
- **Constraint**: sender and receiver must not assign to the same variable

### 2.6 Buffered channel semantics

When channel has capacity > 0:
- `ch!v1,v2`: evaluates values, appends tuple to buffer (blocked if full)
- `ch?x,y`: removes front tuple from buffer, assigns to variables (blocked if empty)
- Sender and receiver act independently (no simultaneous step required)

### 2.7 Effect execution

Effects within one transition are executed **left to right, sequentially**:
```dve
effect x = y, y = x;  // This is NOT a swap! x gets old y, then y gets (new) x.
```

### 2.8 Variable types and overflow

- `byte`: unsigned 8-bit, values 0–255, wraps on overflow (mod 256)
- `int`: signed 32-bit integer
- Boolean interpretation: 0 is false, non-zero is true
- Division by zero is undefined behavior

### 2.9 Assertions

`assert s: expr;` means: whenever the process is in state `s`, `expr` must be non-zero. Violations are detectable during state-space exploration. In XSTS terms, these become invariant properties.

### 2.10 Property process (NOT SUPPORTED — safety only)

When `system async property P;` is declared, process P is a **Büchi automaton** encoding an LTL property. This requires liveness/acceptance-cycle detection, which is **out of scope**.

**The ANTLR parser should still parse property processes and accepting states** (they are valid DVE syntax). However, the **XSTS transformation must reject** models that use them:
- If `DveSystemDecl.propertyProcessName != null`, throw an `UnsupportedOperationException` with a message like: `"Property processes (Büchi automata / LTL liveness) are not supported. Only safety properties via assertions and invariants are handled."`
- If any `DveProcess.acceptingStates` is non-empty in a non-property process, this is technically parseable but meaningless for safety — it can be ignored with a warning.

**Supported safety properties**: assertions (`assert s: expr;`) and externally specified invariants (e.g., `!(P_0.CS && P_1.CS)` passed as an XSTS property separately).

---

## 3. KOTLIN IR (target of ANTLR visitor)

The complete Kotlin data model is provided separately in `DveModel.kt`. Key types:

```
DveModel
  ├── globalVariables: List<DveVarOrArrayDecl>
  ├── channels: List<DveChannelDecl>
  ├── processes: List<DveProcess>
  └── system: DveSystemDecl

DveProcess
  ├── name: String
  ├── variables: List<DveVarOrArrayDecl>
  ├── states: List<String>
  ├── initialState: String
  ├── acceptingStates: List<String>
  ├── committedStates: List<String>
  ├── assertions: List<DveAssertion>
  └── transitions: List<DveTransition>

DveTransition
  ├── sourceState: String
  ├── targetState: String
  ├── guard: DveExpression?
  ├── sync: DveSyncAction?         (Send | Receive)
  └── effects: List<DveAssignment>

DveExpression (sealed)
  ├── LiteralExpr(value: Int)
  ├── VarRefExpr(processName: String?, varName: String)
  ├── ArrayAccessExpr(processName: String?, varName: String, index: DveExpression)
  ├── ProcessStateExpr(processName: String, stateName: String)
  ├── UnaryExpr(op: DveUnaryOp, operand: DveExpression)
  └── BinaryExpr(left: DveExpression, op: DveBinaryOp, right: DveExpression)
```

### Name resolution note

`ProcessName.identifier` is syntactically ambiguous — it could be:
- A qualified variable reference (`ProcessStateExpr` vs `VarRefExpr`)
- Must be resolved after parsing: if `identifier` matches a declared state of `ProcessName`, it's a `ProcessStateExpr`; otherwise it's a `VarRefExpr`

Suggested approach: parse all `X.Y` as a generic `QualifiedRef` node in ANTLR, then resolve to the correct `DveExpression` subtype in a post-parse resolution pass using the collected process state declarations.

---

## 4. XSTS TRANSFORMATION GUIDE

### 4.1 XSTS structure recap

An XSTS (eXtended Symbolic Transition System) in Theta consists of:
- **Variables**: typed (integer, boolean, array)
- **Init**: assignment expression setting initial values
- **Tran**: a nondeterministic choice of guarded transition actions
- **Env**: environment transitions (typically identity for closed systems)
- **Prop**: property to verify (invariant / reachability)

### 4.2 Encoding process control states

For each process P with states {s0, s1, ...}, create an integer variable `P_state` with domain {0, 1, ...}. Map state names to indices.

```
var P_state : integer  // 0 = s0, 1 = s1, ...
```

### 4.3 Encoding variables

- Each global `byte x` → `var x : integer` (with range constraint 0..255 in guards or via type)
- Each local `byte P.y` → `var P_y : integer`
- Each global/local array `byte arr[N]` → N individual integer variables `arr_0, arr_1, ..., arr_{N-1}` (or use Theta array type if supported)

### 4.4 Encoding transitions (async)

Each non-synchronizing transition becomes a choice branch:
```
choice {
    // Process P, transition s0 -> s1 { guard g; effect x = e1, y = e2; }
    assume(P_state == 0 && [g] && [committed_guard]);
    P_state := 1;
    x := [e1];
    y := [e2];
} or {
    // next transition...
}
```

### 4.4b Encoding transitions (sync composition)

In synchronous composition, ALL processes take a step simultaneously. Each global transition is the Cartesian product of one enabled transition per process. A process with no enabled transition blocks the entire system (deadlock).

Encoding: generate all combinations of (one transition per process). Each combination becomes a choice branch where all guards are conjoined and all effects are applied:
```
choice {
    // P1: s0->s1 {guard g1; effect ...}  AND  P2: t0->t1 {guard g2; effect ...}
    assume(P1_state == 0 && P2_state == 0 && [g1] && [g2]);
    P1_state := 1;
    P2_state := 1;
    [effects of P1 transition]
    [effects of P2 transition]
} or {
    // next combination...
}
```

**Warning**: this is exponential in the number of processes — `|T1| × |T2| × ... × |Tn|` combinations. For models with many processes or transitions, this can be extremely large. Consider only generating reachable combinations or using a more compact symbolic encoding.

### 4.5 Encoding synchronous channels

For each pair of (send transition in process A, receive transition in process B) on the same synchronous channel, create a **combined** transition:
```
assume(A_state == sA && B_state == sB && [guardA] && [guardB] && [committed_guard]);
// Evaluate send values
tmp_0 := [send_val_0];
tmp_1 := [send_val_1];
// Apply sender effects
[sender_effects]
// Assign received values
recv_var_0 := tmp_0;
recv_var_1 := tmp_1;
// Apply receiver effects
[receiver_effects]
// Transition both processes
A_state := tA;
B_state := tB;
```

### 4.6 Encoding buffered channels

For each buffered channel with capacity C carrying types T1, ..., Tk:
- Create variables: `ch_count : integer` (0..C), plus `ch_slot_i_j` for slot i field j
- Send: `assume(ch_count < C); ch_slot_{ch_count}_0 := val0; ...; ch_count := ch_count + 1;`
- Receive: `assume(ch_count > 0); var0 := ch_slot_0_0; ...; shift buffer down; ch_count := ch_count - 1;`

Buffer shift requires encoding FIFO rotation, which can be verbose. Consider if Theta supports sequence/array types natively.

### 4.7 Encoding committed state priority

Add a derived condition:
```
val anyCommitted = P1_state == <committed_idx> || P2_state == <committed_idx> || ...
```

For each transition:
- If source state IS committed: no extra guard needed
- If source state is NOT committed: add guard `!anyCommitted`

This ensures committed transitions have strict priority.

### 4.8 Encoding assertions

For `assert s: expr;` in process P:
```
prop: !(P_state == <s_idx> && !([expr]))
// i.e., it should never be the case that P is in state s and expr is false
```

Combine all assertion properties with conjunction for a global invariant.

### 4.9 Unsupported features — MUST FAIL

The XSTS transformation must throw `UnsupportedOperationException` for:

1. **Property processes**: if `DveSystemDecl.propertyProcessName != null`
   - Message: `"Property processes (Büchi/LTL liveness) are not supported. Only safety properties are handled."`

This check should be the **first thing** the transformation does, before any encoding work begins.

Accepting states (`accept`) in non-property processes can be silently ignored (they have no safety semantics).

### 4.10 Init expression

```
init {
    P1_state := 0;  // initial state index
    P2_state := 0;
    x := <initial_value>;
    y := 0;  // default if no initializer
    ch_count := 0;  // all buffers empty
}
```

---

## 5. COMPLETE DVE EXAMPLE

```dve
byte turn = 0;
byte flag[2] = {0, 0};

process P_0 {
    byte j = 0;
    state NCS, CS, wait, q2, q3;
    init NCS;
    trans
        NCS -> q2  { effect flag[0] = 1, j = 1; },
        q2  -> q3  { guard j < 2; },
        q3  -> q2  { guard flag[j] == 0 || turn == 0; effect j = j + 1; },
        q3  -> wait { guard flag[j] != 0 && turn != 0; },
        wait -> q2  { guard flag[j] == 0 || turn == 0; effect j = j + 1; },
        q2  -> CS   { guard j == 2; },
        CS  -> NCS  { effect flag[0] = 0, turn = 1; };
}

process P_1 {
    byte j = 0;
    state NCS, CS, wait, q2, q3;
    init NCS;
    trans
        NCS -> q2  { effect flag[1] = 1, j = 0; },
        q2  -> q3  { guard j < 2; },
        q3  -> q2  { guard flag[j] == 0 || turn == 1; effect j = j + 1; },
        q3  -> wait { guard flag[j] != 0 && turn != 1; },
        wait -> q2  { guard flag[j] == 0 || turn == 1; effect j = j + 1; },
        q2  -> CS   { guard j == 2; },
        CS  -> NCS  { effect flag[1] = 0, turn = 0; };
}

system async;
```

This models Peterson's mutual exclusion for 2 processes. The safety property to check: `!(P_0.CS && P_1.CS)` — both processes should never be in their critical section simultaneously.

---

## 6. EDGE CASES AND NOTES FOR IMPLEMENTATION

1. **Empty transition body**: `s0 -> s1 {}` is valid (no guard, no sync, no effect)
2. **Multiple init/accept/commit declarations**: typically one of each, but the grammar should handle repeated keywords gracefully
3. **Process state names can overlap across processes**: `P1.s0` and `P2.s0` are distinct
4. **Self-loops**: `s0 -> s0 { effect x = x + 1; }` is valid
5. **Array index expressions**: can be arbitrary expressions, not just constants
6. **Negative literals**: DVE has no negative integer literals in the grammar; use unary minus: `-(1)` or `-1` parsed as `UnaryExpr(NEG, LiteralExpr(1))`
7. **The `imply` operator**: some DVE versions support `->` as logical implication in expressions — not standard, can be ignored for core support
8. **`m4` preprocessor macros**: `.mdve` files use m4 macros for parameterized models. The ANTLR parser should only handle already-preprocessed `.dve` files.
9. **Whitespace and newlines**: not significant (C-like)
10. **Semicolons**: terminate clauses inside transition braces and the system declaration. Transition list items are comma-separated, terminated with semicolon after the last one.
11. **Property processes (UNSUPPORTED in XSTS)**: the ANTLR parser must still parse `system async property P;` and `accept` declarations. The XSTS transformation must throw `UnsupportedOperationException` if `propertyProcessName != null`.
