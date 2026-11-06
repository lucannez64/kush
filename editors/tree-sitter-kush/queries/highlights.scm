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
(type_item "row" @keyword)
(impl_item) @keyword
(use_item ["use" "module"] @keyword)
(use_item path: (path (identifier) @namespace))

(primitive_type) @type.builtin
(builtin_type) @type
(builtin_function) @function.builtin

; The receiver, and the return value named in an `ensures` guard
; (`ensures result => { .. }`, `ensures !result => { .. }`).
((identifier) @variable.special
  (#eq? @variable.special "self"))
(_ (keyword) @_ensures . (identifier) @variable.special
  (#eq? @_ensures "ensures") (#eq? @variable.special "result"))
(_ (keyword) @_ensures . (operator) . (identifier) @variable.special
  (#eq? @_ensures "ensures") (#eq? @variable.special "result"))

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
