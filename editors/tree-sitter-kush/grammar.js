/**
 * Tree-sitter grammar for Kush, for editor highlighting, brackets, outline and
 * indentation. It is deliberately tolerant: declarations and bracket nesting
 * are structured, everything else is a flat token stream, so new syntax never
 * breaks highlighting. The `kush lsp` server supplies diagnostics and precise
 * semantic information.
 */
module.exports = grammar({
  name: 'kush',
  extras: $ => [/\s/, $.line_comment, $.block_comment],
  word: $ => $.identifier,
  rules: {
    source_file: $ => repeat($._element),
    _element: $ => choice(
      $.function_item, $.type_item, $.impl_item, $.use_item, $.attribute,
      $.block, $.parenthesized, $.bracketed,
      $.keyword, $.boolean, $.primitive_type, $.builtin_type, $.builtin_function,
      $.string, $.char, $.lifetime, $.number, $.identifier,
      $.operator, $.punctuation,
    ),
    // `fn name` declares a function; a bare `fn(` is a function type or lambda.
    function_item: $ => prec.right(seq('fn', optional(field('name', $.identifier)))),
    type_item: $ => choice(
      seq(field('kind', choice('struct', 'enum', 'trait', 'type', 'effect', 'prop', 'algebra')), field('name', $.identifier)),
      // `effect row Name = { .. };`: `row` is a keyword only here.
      seq(field('kind', 'effect'), 'row', field('name', $.identifier)),
    ),
    impl_item: $ => 'impl',
    use_item: $ => seq(choice('use', 'module'), field('path', $.path)),
    path: $ => seq($.identifier, repeat(seq('.', $.identifier))),
    attribute: $ => seq('#[', repeat(choice($.identifier, $.punctuation, $.parenthesized, $.string, $.number)), ']'),
    block: $ => seq('{', repeat($._element), '}'),
    parenthesized: $ => seq('(', repeat($._element), ')'),
    bracketed: $ => seq('[', repeat($._element), ']'),
    // `total`, `handle` and `invariant` are contextual: identifiers to the
    // grammar, highlighted as keywords by the queries where they act as one.
    keyword: $ => choice('pub', 'foreign', 'let', 'mut', 'return', 'if', 'else', 'match', 'while', 'loop', 'break',
      'continue', 'perform', 'with', 'erased', 'as', 'from', 'in', 'where', 'linear', 'once',
      'ensures', 'is', 'const', 'dyn', 'for'),
    boolean: $ => choice('true', 'false'),
    primitive_type: $ => choice('i8', 'i16', 'i32', 'i64', 'u8', 'u16', 'u32', 'u64', 'f32', 'f64',
      'Bool', 'Unit', 'Char', 'Nat', 'Prop', 'Grade', 'Effects', 'str'),
    builtin_type: $ => choice('IO', 'Bytes', 'String', 'Str', 'Vec', 'Box', 'Arena', 'ArenaBox', 'AllocBox',
      'AllocVec', 'Allocator', 'Task', 'TaskExit', 'Slice', 'DynArray', 'Option', 'Result', 'Stdin', 'Stdout', 'Self'),
    builtin_function: $ => choice('print_i64', 'panic', 'drop', 'refl'),
    identifier: $ => /[A-Za-z_][A-Za-z0-9_]*/,
    lifetime: $ => /'[A-Za-z_][A-Za-z0-9_]*/,
    char: $ => token(seq("'", choice(/[^'\\\n]/, /\\./, /\\u\{[0-9a-fA-F]+\}/), "'")),
    string: $ => seq('"', repeat(choice($.escape_sequence, token.immediate(prec(1, /[^"\\]+/)))), '"'),
    escape_sequence: $ => token.immediate(seq('\\', choice(/u\{[0-9a-fA-F]+\}/, /u[0-9a-fA-F]{4}/, /./))),
    number: $ => token(choice(
      /0[xX][0-9a-fA-F_]+([iu](8|16|32|64))?/,
      /0[bB][01_]+([iu](8|16|32|64))?/,
      /0[oO][0-7_]+([iu](8|16|32|64))?/,
      /[0-9][0-9_]*(\.[0-9][0-9_]*)?([eE][+-]?[0-9]+)?([iu](8|16|32|64)|f32|f64)?/,
    )),
    operator: $ => token(choice('->', '=>', '::', '==', '!=', '<=', '>=', '&&', '||', '<<', '>>', '..',
      '+', '-', '*', '/', '%', '^', '<', '>', '=', '!', '&', '|', '?', '@', '.', '~')),
    punctuation: $ => token(choice(',', ';', ':', '#')),
    line_comment: $ => token(seq('//', /[^\n]*/)),
    block_comment: $ => token(seq('/*', /[^*]*\*+([^/*][^*]*\*+)*/, '/')),
  },
});
