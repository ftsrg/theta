// SMT-LIB 2.6 language definition for Monaco Editor
// Based on CHC-COMP format: https://chc-comp.github.io/format.html

export function registerSmtLib(monaco) {
  monaco.languages.register({ id: 'smtlib' })

  monaco.languages.setMonarchTokensProvider('smtlib', {
    keywords: [
      // Core SMT-LIB commands
      'set-logic', 'set-info', 'set-option', 'get-info', 'get-option',
      'declare-sort', 'declare-const', 'declare-fun', 'define-fun',
      'define-fun-rec', 'define-funs-rec', 'define-sort',
      'declare-datatypes',
      'assert', 'check-sat', 'check-sat-assuming',
      'get-model', 'get-value', 'get-assignment', 'get-proof',
      'get-unsat-core', 'get-unsat-assumptions', 'get-assertions',
      'push', 'pop', 'reset', 'reset-assertions',
      'echo', 'exit',
      // Logic names
      'HORN', 'QF_LIA', 'QF_LRA', 'QF_NIA', 'QF_NRA', 'LIA', 'LRA', 'NIA', 'NRA',
      // Quantifiers and binding
      'forall', 'exists', 'let', 'par',
      // Logical operators
      'and', 'or', 'not', 'xor', 'implies', '=>', 'iff',
      // Comparison
      '=', 'distinct',
      // Arithmetic
      'ite', '+', '-', '*', '/', 'div', 'mod', 'abs', 'rem',
      '<', '<=', '>', '>=',
      // Array theory
      'select', 'store',
      // Type casting
      'as', 'is',
      // Boolean literals
      'true', 'false',
    ],
    
    typeKeywords: [
      'Bool', 'Int', 'Real', 'Array', 'BitVec', 'String', 'RegLan',
    ],

    constants: [
      'true', 'false',
    ],

    operators: [
      '=', '<', '>', '<=', '>=',
      '+', '-', '*', '/',
      '=>', '!',
    ],

    symbols: /[=><!~?:&|+\-*\/\^%@]+/,

    tokenizer: {
      root: [
        // Line comments (semicolon)
        [/;.*$/, 'comment'],

        // Keywords must come before identifiers
        [/[a-zA-Z_!@$%^&*+=<>.?\/~\-][\w!@$%^&*+=<>.?\/~\-]*/, {
          cases: {
            '@keywords': 'keyword',
            '@typeKeywords': 'type',
            '@constants': 'constant',
            '@default': 'identifier'
          }
        }],

        // Strings (double-quoted)
        [/"([^"\\]|\\.)*$/, 'string.invalid'],
        [/"/, 'string', '@string'],

        // Numbers
        [/#x[0-9a-fA-F]+/, 'number.hex'],
        [/#b[01]+/, 'number.binary'],
        [/\d+\.\d+/, 'number.float'],
        [/\d+/, 'number'],

        // Symbols (quoted identifiers)
        [/\|[^|]*\|/, 'identifier.quoted'],

        // Parentheses
        [/[()]/, '@brackets'],

        // Other symbols
        [/@symbols/, {
          cases: {
            '@operators': 'operator',
            '@default': ''
          }
        }],

        // Whitespace
        [/[ \t\r\n]+/, ''],
      ],

      string: [
        [/[^\\"]+/, 'string'],
        [/\\./, 'string.escape'],
        [/"/, 'string', '@pop'],
      ],
    },
  })

  monaco.languages.setLanguageConfiguration('smtlib', {
    comments: {
      lineComment: ';',
    },
    brackets: [
      ['(', ')'],
    ],
    autoClosingPairs: [
      { open: '(', close: ')' },
      { open: '"', close: '"' },
    ],
    surroundingPairs: [
      { open: '(', close: ')' },
      { open: '"', close: '"' },
    ],
  })
}
