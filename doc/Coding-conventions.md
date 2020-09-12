# Coding conventions

We mainly follow the standard Java coding conventions and most of the conventions from the books _Effective Java_ [1] and _Clean Code_ [4]. Some exceptions and additional rules are listed below. Each rule starts with _DO_, _CONSIDER_, _AVOID_ or _DO NOT_, according to [2].

## Source files
* **DO** encode files in UTF-8. **DO NOT** use any other format.

## Naming and formatting

* **DO** use the generally accepted naming and source code formatting conventions of Java (Item 56 of [1], Chapter 1 of [5]). If you are developing in IntelliJ Idea you can import our commonly used formatting profile (see [Development.md](Development.md) for more information).
* **DO** start project names with the prefix `hu.bme.mit.theta`.
* **DO** use CamelCase for class names containing subsequent capital letters, except when the whole name is a sequence of capital letters. Examples: `CFA`, `CfaEdge`, `OsHelper`.
* **CONSIDER** using abbreviations for well known and common names. Examples: `Expression` -> `Expr`, `Statement` -> `Stmt`, `Counterexample` -> `Cex`.

## Creating objects

* **CONSIDER** static factory methods instead of constructors (Item 1 of [1]). This is especially useful for type inference of generic classes.

## Classes and interfaces

* **CONSIDER** making classes immutable if possible (Item 15 of [1]). If initialization of an immutable class seems to be difficult, consider using a builder.
* **CONSIDER** making classes final if they are not designed to be inherited from (Item 17 of [1]).
* **AVOID** unused modifiers, for example methods of interfaces are automatically public.
* **CONSIDER** using the initialization-on-demand holder idiom [3] for lazy loaded, thread safe singletons.
* **CONSIDER** using the weakest types on interfaces. For example, instead of `ArrayList`, use `List`, `Collection` or `Iterable` if possible.

## Testing and verification

* **DO** use JUnit for unit tests.
* **DO** end the name of each unit test class with `Test`. This way, build tools will run your tests automatically.
* **CONSIDER** using parametrized unit tests where possible.
* **CONSIDER** using static analysis tools like FindBugs, SonarQube, PMD.
* **CONSIDER** using `com.google.common.base.Preconditions` methods to check if the preconditions of a method holds. For example: null checks, bound checks, etc. Consider filling the `errorMessage` parameter of these functions with a short error message.

## Other
* **DO NOT** concatenate strings with the `+` operator. Consider `StringBuilder`, `StringJoiner`, `String.format()` instead.
* **AVOID** platform specific constructs. For example, prefer `System.lineSeparator()` over `\r\n` or `\n`.
* **CONSIDER** using `getClass().getSimpleName()` to print the name of a class in its `toString()`. This way, if the class is renamed, `toString()` will also adapt.

# References

1. Joshua Bloch: Effective Java (2nd edition)
1. Krzysztof Cwalina, Brad Abrams: Framework Design Guidelines (2nd edition)
1. https://en.wikipedia.org/wiki/Initialization-on-demand_holder_idiom
1. Robert C. Martin: Clean Code: A Handbook of Agile Software Craftsmanship
1. Robert Liguori, Patricia Liguori: Java 8 Pocket Guide
