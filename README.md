# lang (to be renamed)

`lang` is a C-like programming language designed for the purpose of learning about compiler construction. Examples can be found in the `examples` folder.

## Usage

```
$ cargo run -- -h

Usage: target/debug/lang [options]

Options:
    -h --help           print this help menu
    -t --type TYPE      output type (llvm (default), asm, or obj)
    -o --output FILE    output file name
```

Note that the compiler doesn't automatically link object files (yet), so after generating an object file with the `-t` flag, you can link by running `gcc` on the object file.

## Features

`lang` supports basic variable assignment, function calls, conditionals, loops, arithmetic, and relational operations. The three main types are `int` (a signed 32-bit integer), `string` (a null terminated string), and `bool`. `lang` also supports calling C functions as long as the necessary types are supported.

### In progress features

- Semantic analysis currently reports errors without reporting the location of the error, this will be fixed
- Add floating point and unsigned integer types of different widths
- Allow function definitions in any order
- Scope (currently everything inside a function is in the same scope)
- Arrays
- For loops (only while loops are supported at the moment)
- Allow parenthesis in expressions

### Long term features

- Dynamic memory
- Optional garbage collections
- Algebraic data types and pattern matching
