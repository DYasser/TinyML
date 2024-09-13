# TinyML
TinyML is a simple interpreter for the core operations described in the metalanguage ML.

The aim of this project is to implement the algorithm of type inference.

This is a porting of the existing repository of my professor [Alvise Sapnò](https://github.com/alvisespano/FL-unipd-2021-22).

The main reason of this porting is to use the dotnet cli for executing the entire program, and not be oblige to use the Visual Studio IDE.

## Implementation
The skeleton already contains:
- **Lexer**: parses the source code into tokens (Lexer.fsl);
- **Parser**: receives the output of the lexer as input and produces an Abstract Syntax Tree (Parsers.fsy);
- **Type checker**: checks the types of the expressions (Typing.fs);
- **Evaluator**: evaluates the expressions (Eval.fs).

The goal of the project was to implement a type inference algorithm, to be used while checking the correctness of the types of the expressions.

## Installation
You can simply clone the repo using the command `git clone https://github.com/DYasser/TinyML`.

## Usage

* `dotnet build` to compile the interpreter

* `dotnet run` to use the interpreter in interactive mode

* `dotnet run <name-of-file.tml>` to evaluate all the expression inside the *".tml"* file.

## License
[MIT](https://choosealicense.com/licenses/mit/)
