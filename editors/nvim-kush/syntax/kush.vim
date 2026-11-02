" Fallback syntax for Kush when the language server is not attached; the
" server's semantic tokens take over when it is.
" Reserved words (Kind variants and contextual identifiers).
syntax keyword kushKeyword use let mut return if else while loop break continue match enum
syntax keyword kushKeyword struct type module erased handle perform with total
syntax keyword kushKeyword pub trait impl prop effect row foreign test
syntax keyword kushBoolean true false

" Strings, characters, and numbers.
syntax region kushString start=+"+ end=+"+ skip=+\\"+ containedin=ALLBUT,kushComment,kushBlockComment
syntax match kushChar "'[^']*'"
syntax match kushNumber '\<\d\(_\d\)*\>'
syntax match kushFloat '\<\d\(_\d\)*\.\d\(_\d\)*\>'
syntax match kushLifetime "'[A-Za-z_][A-Za-z0-9_]*\>"
syntax match kushComment '//.*$' contains=@Spell
syntax region kushBlockComment start='/\*' end='\*/' contains=kushBlockComment,@Spell

" Primitives and well-known namespaces.
syntax keyword kushType i8 i16 i32 i64 u8 u16 u32 u64 f64 bool char String Bytes Nat Prop
syntax match kushNamespace '\<[A-Za-z_][A-Za-z0-9_]*\.[A-Za-z_]\+'ms=s+1
syntax match kushDecorator '#\[\w\+'
syntax match kushEffect '! *{[^}]*}\|![^ ]*' containedin=ALLBUT,kushComment,kushBlockComment

highlight default link kushKeyword Keyword
highlight default link kushBoolean Boolean
highlight default link kushString String
highlight default link kushChar Character
highlight default link kushNumber Number
highlight default link kushFloat Float
highlight default link kushComment Comment
highlight default link kushBlockComment Comment
highlight default link kushType Type
highlight default link kushNamespace Function
highlight default link kushEffect Special
highlight default link kushDecorator Special
highlight default link kushLifetime Type

let b:current_syntax = 'kush'
