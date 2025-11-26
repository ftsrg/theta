// XSTS language definition for Monaco Editor
// Based on: https://github.com/ftsrg/theta/blob/master/subprojects/xsts/xsts/src/main/antlr/XstsDsl.g4

export function registerXsts(monaco) {
  monaco.languages.register({ id: 'xsts' })

  monaco.languages.setMonarchTokensProvider('xsts', {
    keywords: [
      // Control structures
      'if', 'then', 'else', 'choice', 'or', 'for', 'from', 'to', 'do',
      // Statements
      'assume', 'havoc', 'local',
      // Declarations
      'type', 'var', 'ctrl',
      // Sections
      'init', 'trans', 'env', 'prop',
      // Logical operators (as keywords)
      'iff', 'xor',
      // Arithmetic operators
      'rem',
      // Type keywords
      'boolean', 'integer',
      // Literals
      'true', 'false', 'default',
    ],

    operators: [
      ':=', '==', '!=', '<', '>', '<=', '>=',
      '+', '-', '*', '/', '%',
      '&&', '||', '!',
      '=>',
      '<-', '->',
      '=', ':',
    ],

    symbols: /[=><!~?:&|+\-*\/\^%<>\[\]]+/,

    tokenizer: {
      root: [
        // Line comments
        [/\/\/.*$/, 'comment'],
        
        // Block comments
        [/\/\*/, 'comment', '@comment'],

        // Strings
        [/"([^"\\]|\\.)*$/, 'string.invalid'],
        [/"/, 'string', '@string'],

        // Numbers (only decimal integers in XSTS grammar)
        [/\d+/, 'number'],

        // Identifiers and keywords (ID can contain $ and .)
        [/[a-zA-Z_$][a-zA-Z0-9_$.]*/, {
          cases: {
            '@keywords': 'keyword',
            '@default': 'identifier'
          }
        }],

        // Delimiters and operators
        [/[{}()\[\]]/, '@brackets'],
        [/[;,.]/, 'delimiter'],
        [/@symbols/, {
          cases: {
            '@operators': 'operator',
            '@default': ''
          }
        }],

        // Whitespace
        [/[ \t\r\n]+/, ''],
      ],

      comment: [
        [/[^\/*]+/, 'comment'],
        [/\*\//, 'comment', '@pop'],
        [/[\/*]/, 'comment'],
      ],

      string: [
        [/[^\\"]+/, 'string'],
        [/\\./, 'string.escape'],
        [/"/, 'string', '@pop'],
      ],
    },
  })

  monaco.languages.setLanguageConfiguration('xsts', {
    comments: {
      lineComment: '//',
      blockComment: ['/*', '*/'],
    },
    brackets: [
      ['{', '}'],
      ['[', ']'],
      ['(', ')'],
    ],
    autoClosingPairs: [
      { open: '{', close: '}' },
      { open: '[', close: ']' },
      { open: '(', close: ')' },
      { open: '"', close: '"' },
    ],
    surroundingPairs: [
      { open: '{', close: '}' },
      { open: '[', close: ']' },
      { open: '(', close: ')' },
      { open: '"', close: '"' },
    ],
    folding: {
      markers: {
        start: /^\s*\/\/\s*#?region\b/,
        end: /^\s*\/\/\s*#?endregion\b/,
      },
    },
  })
}
