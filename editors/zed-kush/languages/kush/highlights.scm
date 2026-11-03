(line_comment) @comment
(block_comment) @comment
(string) @string
(escape_sequence) @string.escape
(char) @string.special
(number) @number
(boolean) @boolean
(lifetime) @label
(attribute) @attribute

(keyword) @keyword
(function_item "fn" @keyword)
(type_item kind: _ @keyword)
(impl_item) @keyword
(use_item ["use" "module"] @keyword)
(use_item path: (path (identifier) @namespace))

(primitive_type) @type.builtin
(builtin_type) @type
(builtin_function) @function.builtin

(function_item name: (identifier) @function)
(type_item name: (identifier) @type)

; Calls: a name directly followed by an argument list.
(_ (identifier) @function . (parenthesized))

; Capitalized names are types, variants, and constructors.
((identifier) @type
  (#match? @type "^[A-Z]"))

(operator) @operator
(punctuation) @punctuation.delimiter
["(" ")" "[" "]" "{" "}" "#["] @punctuation.bracket
