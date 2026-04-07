# Logging

Theta uses a singleton `Logger` object for all logging. It is defined in the `hu.bme.mit.theta.common.logging` package.

## Initialization

`Logger.init()` must be called once before any logging. It accepts a case-insensitive regex pattern that selects which log levels to enable.

```java
Logger.init("ERROR|WARN|RESULT|BENCHMARK|MAINSTEP|SUBSTEP");
```

To enable all log levels, use the `Logger.ALL` constant:

```java
Logger.init(Logger.ALL);
```

By default, output goes to stderr. To log to a file instead:

```java
Logger.init("ERROR|WARN|INFO", "/path/to/logfile.log");
```

## Log Levels

| Method | Level Name | Use Case |
|--------|-----------|----------|
| `Logger.error(...)` | ERROR | Errors and failures |
| `Logger.errorOnce(...)` | ERROR | Errors that should only appear once |
| `Logger.warn(...)` | WARN | Warnings |
| `Logger.warnOnce(...)` | WARN | Warnings that should only appear once |
| `Logger.result(...)` | RESULT | Final verification results |
| `Logger.benchmark(...)` | BENCHMARK | Timing and performance metrics |
| `Logger.mainStep(...)` | MAINSTEP | Major algorithm steps (e.g., CEGAR iterations) |
| `Logger.subStep(...)` | SUBSTEP | Sub-steps within a major step |
| `Logger.info(...)` | INFO | General information |
| `Logger.infoOnce(...)` | INFO | Information that should only appear once |
| `Logger.detail(...)` | DETAIL | Detailed information |
| `Logger.verbose(...)` | VERBOSE | Verbose output |
| `Logger.solverDebug(...)` | DEBUG_SOLVER | Solver communication debug |
| `Logger.debug(...)` | DEBUG | General debug output |

## Formatting

All log methods accept printf-style format strings:

```java
Logger.info("Found %d items in %s", count, name);
Logger.mainStep("Starting iteration %d", iteration);
```

For messages without arguments, the format string is used directly without `String.format` overhead:

```java
Logger.info("Starting analysis");
```

## *Once Variants

`warnOnce`, `infoOnce`, and `errorOnce` deduplicate messages. The same formatted message is only logged once per session, regardless of how many times the method is called.

```java
Logger.warnOnce("Unsupported feature X in %s", file);
```

This is useful for warnings inside loops or frequently called methods where the same warning would otherwise be repeated many times.

## Checking Enabled Levels

Use `Logger.isEnabled(...)` to guard expensive operations before logging:

```java
if (Logger.isEnabled(Logger.Level.VERBOSE)) {
    Logger.verbose("Complex state: %s", expensiveToString());
}
```

## Disabling Logging at Build Time

To compile a release build with all logging completely eliminated:

```bash
./gradlew build -PnoLogging
```

This replaces the `Logger` implementation with empty method bodies at compile time. Every `Logger.*` call becomes a no-op with zero runtime overhead -- no stack traces, no formatting, no I/O. The `init()` call is also a no-op, so existing code does not need to change.

The default build (without `-PnoLogging`) includes full logging support.

## Adding a New Log Level

1. Add an entry to the `Level` enum in `subprojects/common/common/src/main/templates/Logger.enabled.kt`:

```kotlin
MY_LEVEL("MY_LEVEL"),
```

2. Add a convenience method in the same file:

```kotlin
@JvmStatic
fun myLevel(format: String, vararg args: Any?) {
    if (!requireInit()) return
    log(Level.MY_LEVEL, format, *args)
}
```

3. Add the level name to the `ALL` constant:

```kotlin
const val ALL = "ERROR|WARN|RESULT|BENCHMARK|MAINSTEP|SUBSTEP|INFO|DETAIL|VERBOSE|DEBUG_SOLVER|MY_LEVEL"
```

4. Add the matching empty method to `subprojects/common/common/src/main/templates/Logger.disabled.kt`:

```kotlin
@JvmStatic
fun myLevel(format: String, vararg args: Any?) {}
```

5. Users can now enable it via the pattern: `Logger.init("ERROR|MY_LEVEL")`.
