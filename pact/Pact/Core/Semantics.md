# Pact Semantics document

This document should serve as a record of known Pact semantics, covering as much of the language as possible, including
corner cases, and semantic divergences between core and prod Pact.

Bullet points that are not filled are potential tasks.

## Pact Syntax

Approximate (in-progress) grammar definition of Pact
in [Extended Backus-Naur form (EBNF)](https://en.wikipedia.org/wiki/Extended_Backus–Naur_form).

### Legend

| Usage         | Notation  | Meaning                               |
|---------------|:---------:|---------------------------------------|
| concatenation |           | One token immediately follows another |
| alternation   |    \|     | One or the other                      |
| optional      | \[ ... \] | none or once                          |
| repetition    | \{ ... \} | none or many                          |
| grouping      | \( ... \) | Groups tokens to match                |

### Lexical Syntax

```
lower          ::= 'a' | ... | 'z' // Ascii only, no unicode lower case
upper          ::= 'A' | ... | 'Z' // Ascii only, no unicode lower case
special-symbol ::= '%' | '#' | '+' | '-' | '_' | '&' | '$' | '@'
                     | '<' | '>' | '=' | '^' | '?' | '*' | '!'
                     | '|' | '/' | '~'
alpha          ::= lower | upper
parens         ::=  '(' | ')'
brackets       ::= '[' | ']'
braces         ::= '{' | '}'
digit          ::= '0' | ... | '9'
comment        ::= ';' "any sequence of characters up until newline"
colon          ::= ':'
bind-assign    ::= ':' '='
dot            ::= '.'
comma          ::= ','
nl             ::= "new line character"
IDENT          ::= (alpha | special-symbol) {alpha | special-symbol | digit}
STRING         ::= '"' {any character that is not a line break} '"'
TICKSTRING     ::= '\'' alpha {alpha | digit | '-' | '_'}
```

### Keywords

|             |                    |                   |
|:-----------:|:------------------:|:-----------------:|
|     let     |        let*        |        if         |
|    defun    |       defcap       |     defconst      |
|  defschema  |      deftable      |      defpact      |
| defproperty |      property      |     invariant     |
|  interface  |       module       |       bless       |
| implements  |        use         |       true        |
|    false    |       lambda       |        and        |
|     or      |        load        |       @doc        |
|   @model    |       @event       |     @managed      |
|    step     | step-with-rollback |      enforce      |
| enforce-one |  with-capability   | create-user-guard |
|     try     |       error        |       progn       |

##### In Progress

```javascript
/* Whitespace */
CRLF="regexp:\R"
WHITE_SPACE="regexp:[ \n\t\f]"

/* Comments */
COMMENT="regexp:(;.*\n*)"

/* Keywords */
KEYWORD_BLESS="bless"
KEYWORD_ENFORCE="enforce"
KEYWORD_ENFORCE_ONE="enforce-one"
KEYWORD_IF="if"
KEYWORD_IMPLEMENTS="implements"
KEYWORD_INTERFACE="interface"
KEYWORD_LAMBDA="lambda"
KEYWORD_LET="regexp:(let\*?)"
KEYWORD_MODULE="module"
KEYWORD_BLOCK_INTRO="progn"
KEYWORD_STEP="step"
KEYWORD_STEP_WITH_ROLLBACK="step-with-rollback"
KEYWORD_SUSPEND="suspend"
KEYWORD_TRY="try"
KEYWORD_IMPORT="use"

/* Keywords (Capabilities) */
KEYWORD_CREATE_USER_GUARD="create-user-guard"
KEYWORD_WITH_CAPABILITY="with-capability"

/* Keywords (Definitions) */
KEYWORD_DEF_CAP="defcap"
KEYWORD_DEF_CONST="defconst"
KEYWORD_DEF_PACT="defpact"
KEYWORD_DEF_SCHEMA="defschema"
KEYWORD_DEF_TABLE="deftable"
KEYWORD_DEFUN="defun"

/* Keywords (REPL) */
KEYWORD_LOAD="load"

/* Annotations */
KEYWORD_DOC_ANNOTATION="@doc"
KEYWORD_EVENT_ANNOTATION="@event"
KEYWORD_MANAGED_ANNOTATION="@managed"
KEYWORD_MODEL_ANNOTATION="@model"

/* Literals */
STR="regexp:(\"([^\"\\]|\\\"|\\)*\")"
INTEGER="regexp:([+-]?[0-9]+)"
FLOATING_POINT="regexp:([+-]?([0-9]+\.[0-9]*|\.[0-9]+)([eE][+-]?[0-9]+)?)"
TRUE="true"
FALSE="false"

/* Identifiers */
TICK="regexp:'[a-zA-Z][a-zA-Z0-9\-_]*"
IDENTIFIER="regexp:[a-zA-Z_][a-zA-Z0-9\-_]*"

/* Operators (Arithmetic) */
PLUS="+"
MINUS="-"
MULTIPLY="*"
DIVIDE="/"
POW="^"
ABS="abs"
CEILING="ceiling"
FLOOR="floor"
LOG="log"
LN="ln"
DECIMAL="dec"
EXP="exp"
MOD="mod"
ROUND="round"
SQRT="sqrt"

/* Operators (Assignment) */
BIND_ASSIGN=":="

/* Operators (Bitwise) */
BITWISE_AND="&"
BITWISE_OR="|"
BITWISE_REVERSE="~"
BITWISE_SHIFT="shift"
BITWISE_XOR="xor"

/* Operators (Logical) */
AND="and"
AND_SHORT_CIRCUIT="and?"
NOT="not"
NOT_SHORT_CIRCUIT="not?"
OR="or"
OR_SHORT_CIRCUIT="or?"

/* Operators (Relational) */
EQUAL="="
NOT_EQUAL="!="
LESS_THAN="<"
LESS_THAN_OR_EQUAL="<="
GREATER_THAN=">"
GREATER_THAN_OR_EQUAL=">="

/* Delimiters */
PAREN_OPEN="("
PAREN_CLOSE=")"
BRACE_OPEN="{"
BRACE_CLOSE="}"
BRACKET_OPEN="["
BRACKET_CLOSE="]"
COLON=":"
COMMA=","
DOT="."
DYN_ACC="::"
```

#### Productions

```bnf
Program ::= ReplProgramList
          | ProgramList

/* Top Level */

ProgramList ::= TopLevel+

TopLevel ::= Module
           | Interface
           | Use
           | Expression

/* Top Level (REPL) */

ReplProgramList ::= ReplTopLevel+

ReplTopLevel ::= ReplSpecial
               | Defun
               | DefConst
               | TopLevel

ReplSpecial ::= "(" KEYWORD_LOAD STR Boolean? ")"

/* Annotations & Documentation */

MDocOrModel ::= DocumentationAnnotation ModelAnnotation
              | ModelAnnotation DocumentationAnnotation
              | DocumentationAnnotation
              | ModelAnnotation
              | DocumentationString

MDCapMeta ::= ManagedAnnotation
            | EventAnnotation

MModel ::= ModelAnnotation

MDoc ::= DocumentationAnnotation
       | DocumentationString

DocumentationAnnotation ::= KEYWORD_DOC_ANNOTATION STR

DocumentationString ::= STR

EventAnnotation ::= KEYWORD_EVENT_ANNOTATION

ManagedAnnotation ::= KEYWORD_MANAGED_ANNOTATION (IDENTIFIER ParsedName)*

ModelAnnotation ::= KEYWORD_MODEL_ANNOTATION "[" PactFVModels "]"

/* Module */

Module ::= "(" KEYWORD_MODULE IDENTIFIER Governance [MDocOrModel] (Definition | Extension)+ ")"

ModuleNames ::= ModuleQualifier ("," ModuleQualifier)*

Governance ::= String
             | IDENTIFIER

Interface ::= "(" KEYWORD_INTERFACE IDENTIFIER [MDocOrModel] (InterfaceDefinition | Use)+ ")"

/* Extensions */

Extension ::= Use
            | "(" KEYWORD_IMPLEMENTS ModuleQualifier ")"
            | "(" KEYWORD_BLESS String ")"

Use ::= "(" KEYWORD_IMPORT ModuleQualifier STR? ImportList? ")"

ImportList ::= "[" [IDENTIFIER+] "]"

/* Definitions */

Definition ::= DefCap
             | DefConst
             | DefPact
             | DefSchema
             | DefTable
             | Defun

DefCap    ::= "(" KEYWORD_DEF_CAP IDENTIFIER [MTypeAnn] "(" [MArgs] ")" [MDocOrModel] [MDCapMeta] Block ")"
DefConst  ::= "(" KEYWORD_DEF_CONST IDENTIFIER [MTypeAnn] Expression [MDoc] ")"
DefPact   ::= "(" KEYWORD_DEF_PACT IDENTIFIER [MTypeAnn] "(" MArgs ")" [MDocOrModel] Steps ")"
DefSchema ::= "(" KEYWORD_DEF_SCHEMA IDENTIFIER [MDocOrModel] SchemaArgumentList ")"
DefTable  ::= "(" KEYWORD_DEF_TABLE IDENTIFIER ":" "{" ParsedName "}" [MDoc] ")"
Defun     ::= "(" KEYWORD_DEFUN IDENTIFIER [MTypeAnn] "(" [MArgs] ")" [MDocOrModel] Block ")"

MArgs ::= MArg*

MArg ::= IDENTIFIER ":" TypeDeclaration
       | IDENTIFIER

MTypeAnn ::= ":" TypeDeclaration

SchemaArgumentList ::= SchemaArgument (SchemaArgument)*

SchemaArgument ::= IDENTIFIER (":" TypeDeclaration)?

/* Definitions (Interface) */

InterfaceDefinition ::= IfDefCap
                      | DefConst
                      | IfDefPact
                      | DefSchema
                      | IfDefun

IfDefCap  ::= "(" KEYWORD_DEF_CAP IDENTIFIER [MTypeAnn] "(" MArgs ")" [MDocOrModel] [MDCapMeta] ")"
IfDefPact ::= "(" KEYWORD_DEF_PACT IDENTIFIER [MTypeAnn] "(" MArgs ")" [MDocOrModel] ")"
IfDefun   ::= "(" KEYWORD_DEFUN IDENTIFIER [MTypeAnn] "(" MArgs ")" [MDocOrModel] ")"

/* Expressions */

Block ::= BlockBody

BlockBody ::= Expression+

Expression ::= "(" SymbolicExpression ")"
             | Variable
             | DataType
             | Operator

SymbolicExpression ::= LambdaExpression
                     | LetExpression
                     | IfExpression
                     | TryExpression
                     | SuspendExpression
                     | ProgNExpression
                     | CapabilityExpression
                     | GenericExpression

LambdaExpression ::= KEYWORD_LAMBDA "(" LambdaArguments ")" Block

LambdaArguments ::= LambdaArgument (LambdaArgument)*

LambdaArgument ::= IDENTIFIER (":" TypeDeclaration)?

LetExpression ::= KEYWORD_LET "(" Binders ")" Block

Binders ::= ("(" IDENTIFIER [MTypeAnn] Expression ")")+

IfExpression ::= KEYWORD_IF Expression Expression Expression

TryExpression ::= KEYWORD_TRY Expression Expression

SuspendExpression ::= KEYWORD_SUSPEND Expression

ProgNExpression ::= KEYWORD_BLOCK_INTRO BlockBody

CapabilityExpression ::= CapabilityForm

CapabilityForm ::= KEYWORD_WITH_CAPABILITY Expression Block
                 | KEYWORD_CREATE_USER_GUARD "(" ParsedName AppList ")"

AppList ::= Expression*

GenericExpression ::= Expression AppBindList

AppBindList ::= (Expression | BindingForm)*

BindingForm ::= "{" BindPairs "}"

BindPairs ::= BindPair ("," BindPair)*

BindPair ::= STR ":=" MArg
           | TICK ":=" MArg

/* Steps */

Steps ::= Step+

Step ::= "(" KEYWORD_STEP Expression [MModel] ")"
       | "(" KEYWORD_STEP Expression Expression [MModel] ")"
       | "(" KEYWORD_STEP_WITH_ROLLBACK Expression Expression [MModel] ")"
       | "(" KEYWORD_STEP_WITH_ROLLBACK Expression Expression Expression [MModel] ")"

/* Variables & Names */

Variable ::= IDENTIFIER "." ModuleQualifier
           | IDENTIFIER "::" IDENTIFIER
           | IDENTIFIER

ParsedName ::= IDENTIFIER "." ModuleQualifier
             | IDENTIFIER "::" IDENTIFIER
             | IDENTIFIER

ParsedTypeName ::= IDENTIFIER "." ModuleQualifier
                 | IDENTIFIER

ModuleQualifier ::= IDENTIFIER "." IDENTIFIER
                  | IDENTIFIER

/* Data Types */

TypeDeclaration ::= "[" TypeDeclaration "]"
                  | "module" "{" ModuleNames "}"
                  | IDENTIFIER "{" ParsedTypeName "}"
                  | IDENTIFIER

DataType ::= CompositeDataType
           | AtomicDataType
           | "(" ")"

CompositeDataType ::= List
                    | Object

AtomicDataType ::= Number
                 | String
                 | Boolean

/* Data Types (Composite) */

List ::= "[" [ListExpression] "]"

ListExpression ::= Expression MCommaExpression?

MCommaExpression ::= "," ExpressionCommaSep
                   | AppList

ExpressionCommaSep ::= Expression ("," Expression)*

Object ::= "{" ObjectBody? "}"

ObjectBody ::= FieldPair ("," FieldPair)*

FieldPair ::= STR ":" Expression
            | TICK ":" Expression

/* Data Types (Atomic) */

Number ::= FLOATING_POINT
         | INTEGER

String ::= STR
         | TICK

Boolean ::= TRUE
          | FALSE

/* Operators */

Operator ::= ArithmeticOperator
           | AssignmentOperator
           | LogicalOperator
           | RelationalOperator
           | BitwiseOperator
           | KEYWORD_ENFORCE
           | KEYWORD_ENFORCE_ONE

ArithmeticOperator ::= PLUS
                     | MINUS
                     | MULTIPLY
                     | DIVIDE
                     | POW
                     | ABS
                     | CEILING
                     | FLOOR
                     | LOG
                     | LN
                     | DECIMAL
                     | EXP
                     | MOD
                     | ROUND
                     | SQRT

AssignmentOperator ::= BIND_ASSIGN

BitwiseOperator ::= BITWISE_AND
                  | BITWISE_OR
                  | BITWISE_REVERSE
                  | BITWISE_SHIFT
                  | BITWISE_XOR

LogicalOperator ::= AND
                  | AND_SHORT_CIRCUIT
                  | NOT
                  | NOT_SHORT_CIRCUIT
                  | OR
                  | OR_SHORT_CIRCUIT

RelationalOperator ::= EQUAL
                     | NOT_EQUAL
                     | LESS_THAN
                     | LESS_THAN_OR_EQUAL
                     | GREATER_THAN
                     | GREATER_THAN_OR_EQUAL

PactFVModels ::= PropExpressionList

PropExpressionList ::= PropExpression*

PropExpression ::= PropAtom
                 | "(" PropExpressionList ")"
                 | "[" PropExpressionList "]"

PropAtom ::= Variable
           | Number
           | String
           | FVKeyword
           | FVDelim
           | Boolean
           | Operator

FVKeyword ::= "let"
            | "lambda"
            | "if"
            | "progn"
            | "suspend"
            | "try"
            | "enforce"
            | "enforce-one"
            | "and"
            | "or"
            | "create-user-guard"
            | "with-capability"

FVDelim ::= "{"
          | "}"
          | ":"
          | ","
```

## Modules

### Module Lexing and Parsing Implementation

- [x] `module` keyword
- [x] Governance forms: keyed governance (via Keyset name string) or cap governance bare name resolution
- [x] use, bless and implements forms
- [x] defuns, defconsts, defcaps
- [x] defschema, deftable
- [x] defpacts

### Module name resolution

- [x] Defuns
- [x] DefConsts
- [x] DefCaps
- [x] DefSchemas
- [x] DefTables
- [x] Defpacts
- [x] Internal defs produce the right dependency tree (Needs test)

### Module evaluation semantics

- [x] Module governance eval (Note: the way we do this via interpretation is still not concrete)
    - [x] Cap governance
    - [x] Keyset Governance

## Top level forms

### Defuns

- [x] Defun name resolution
- [x] Defconst name resolution
- [x] Defcap name resolution
- [x] DefSchema name resolution
- [x] DefTable name resolution
- [x] DefPact name resolution

## Environment

### EvalEnv

- [x] Message signatures
- [x] Pactdb in env
- [x] Tx hash
- [x] Execution Mode
- [x] Pact Step
- [x] Chain data
- [ ] Gas ref (In eval env? Unsure whether this will be abstracted out via `MonadGas`)
- [ ] Gas Env? Also not sure, see above ^
- [x] Runtime Flags
- [ ] Warnings
- [ ] SPV Support
- [x] Purity (now in pactdb)

### EvalState

- [x] Loaded names (called `Loaded` currently instead of `RefStore` and `RefState`)
- [x] Call stack
- [x] Capabilities environment
- [ ] Gas log
- [x] Pact Events
- [x] Defpact environment  `PactExec`

### Environment semantic changes

- RefStore no longer in `EvalEnv`. We do not resolve natives that way, but we potentially could for repl natives in
  modules. It is TBD
- `InRepl` flag is not necessary currently. This may change, but it serves as a way to fork on-chain errors in
  prod-pact.

## Intepreter

- [X] Stable interpreter API
- [ ] EvalResult and EvalInput-type API

## Base Builtins

### at

- [x] Object case implemented
- [x] List case implemented
- [ ] Gas

### base64-decode

- [x] implemented
- [ ] Gas

### base64-encode

- [x] implemented
- [ ] Gas

### bind

- [x] implemented
- [ ] Gas

### chain-data

- [x] implemented
- [ ] Gas

### compose

- [x] implemented
- [ ] Gas

### concat

- [x] implemented
- [ ] Gas

### constantly

- [x] implemented
- [ ] Gas

### contains

- [x] String case implemented
- [x] List case implemented
- [x] Object case implemented
- [ ] Gas

### define-namespace

- [x] implemented
- [x] repl test
- [ ] Gas

### distinct

- [x] implemented
- [ ] Gas

### enforce

- [x] implemented
- [ ] Gas

### enforce-one

- [x] implemented
- [ ] Gas

### enforce-pact-version

TODO: Do we want this still???

### enumerate

- [x] implemented 2-arg overload
- [x] implemented 3-arg overload
- [ ] Gas

### filter

- [x] implemented
- [ ] Gas

### fold

- [x] implemented
- [ ] Gas

### format

- [x] implemented
- [ ] Gas

### hash

- [x] implemented
- [ ] Gas

### identity

- [x] implemented
- [ ] Gas

### if

- [x] implemented
- [ ] Gas

### int-to-str

- [x] implemented
- [ ] Gas

### is-charset

- [x] implemented
- [ ] Gas

### length

- [x] object case implemented
- [x] string case implemented
- [x] list case implemented
- [ ] Gas

### list

DELETED FROM EXISTENCE

### list-modules

TODO: (potentially) DELETED FROM EXISTENCE

### make-list

- [x] implemented
- [ ] Gas

### map

- [x] implemented
- [ ] Gas

### pact-id

- [x] implemented
- [ ] Gas

### pact-version

TODO: (potentially) DELETED FROM EXISTENCE

### public-chain-data

- Todo: provide in base loaded

### read-decimal

- [x] implemented
- [ ] Gas

### read-integer

- [x] implemented
- [ ] Gas

### read-msg

- [x] implemented both overloads
- [ ] Gas

### read-string

- [x] implemented
- [ ] Gas

### remove

- [x] implemented
- [ ] Gas

### resume

- [x] implemented
- [ ] Gas

### reverse

- [x] implemented
- [ ] Gas

### reverse

- [x] list case implemented
- [x] object case implemented
- [ ] Gas

### str-to-int

- [x] list case implemented
- [x] object case implemented
- [ ] Gas

### str-to-list

- [x] implemented
- [ ] Gas

### take

- [x] string case implemented
- [x] list case implemented
- [ ] Gas

### try

- [x] implemented
- [ ] Gas

### tx-hash

- [x] implemented
- [ ] Gas

### typeof

- [x] implemented
- [ ] Gas

### where

- [x] implemented
- [ ] Gas

### yield

- [x] implemented both overloads (yield and yield to chain)
- [ ] Gas

### zip

- [x] implemented both overloads (yield and yield to chain)
- [ ] Gas

### create-table

- [x] Local Bypass Check (NOTBYPASSED)
- [x] Enforcing blessed hashes
- [x] Guarded db access (Module admin or calledByModule)
- [x] Mock PactDb implementation
- [ ] ChainwebPactDb implementation
- [x] implemented
- [ ] Gas

### describe-keyset

- [x] Enforced top level only
- [x] Mock PactDb implementation
- [ ] ChainwebPactDb implementation
- [x] implemented
- [ ] Gas

### describe-module

- [x] Local only
- [x] Enforced top level only
- [x] Mock PactDb implementation
- [ ] ChainwebPactDb implementation
- [x] implemented
- [ ] Gas

### fold-db

- [x] Local Bypass Check  (BYPASS)
- [x] Enforcing blessed hashes
- [x] Guarded db access (Module admin or calledByModule)
- [x] Mock PactDb implementation
- [ ] ChainwebPactDb implementation
- [x] implemented
- [ ] Gas

### insert

- [x] Local Bypass Check (NOTBYPASSED)
- [x] Enforcing blessed hashes
- [x] Guarded db access (Module admin or calledByModule)
- [x] Mock PactDb implementation
- [ ] ChainwebPactDb implementation
- [x] implemented
- [ ] Gas

### keylog

- [x] Local only
- [x] Local Bypass Check (BYPASS)
- [x] Enforcing blessed hashes
- [x] Guarded db access (Module admin or calledByModule)
- [x] Mock PactDb implementation
- [ ] ChainwebPactDb implementation
- [x] implemented
- [ ] Gas

### keys

- [x] Local Bypass Check (BYPASS)
- [x] Enforcing blessed hashes
- [x] Guarded db access (Module admin or calledByModule)
- [x] Mock PactDb implementation
- [ ] ChainwebPactDb implementation
- [x] implemented
- [ ] Gas

### read

- [x] Local Bypass Check (BYPASS)
- [x] Enforcing blessed hashes
- [x] Guarded db access (Module admin or calledByModule)
- [x] Mock PactDb implementation
- [ ] ChainwebPactDb implementation
- [x] implemented
- [ ] Gas

### select

- [x] Local Bypass Check (BYPASS)
- [x] Enforcing blessed hashes
- [x] Guarded db access (Module admin or calledByModule)
- [x] Mock PactDb implementation
- [ ] ChainwebPactDb implementation
- [x] implemented
- [ ] Gas

### txids

- [x] Local only
- [x] Local Bypass Check (BYPASS)
- [x] Enforcing blessed hashes
- [x] Guarded db access (Module admin or calledByModule)
- [x] Mock PactDb implementation
- [ ] ChainwebPactDb implementation
- [x] implemented
- [ ] Gas

### txlog

- [x] Local only
- [x] Local Bypass Check (BYPASS)
- [x] Enforcing blessed hashes
- [x] Guarded db access (Module admin or calledByModule)
- [x] Mock PactDb implementation
- [ ] ChainwebPactDb implementation
- [x] implemented
- [ ] Gas

### update

- [x] Local Bypass Check (NOTBYPASSED)
- [x] Enforcing blessed hashes
- [x] Guarded db access (Module admin or calledByModule)
- [x] Mock PactDb implementation
- [ ] ChainwebPactDb implementation
- [x] implemented
- [ ] Gas

### with-default-read

- [x] Local Bypass Check (BYPASS)
- [x] Enforcing blessed hashes
- [x] Guarded db access (Module admin or calledByModule)
- [x] Mock PactDb implementation
- [ ] ChainwebPactDb implementation
- [x] implemented
- [ ] Gas

### with-read

- [x] Local Bypass Check (BYPASS)
- [x] Enforcing blessed hashes
- [x] Guarded db access (Module admin or calledByModule)
- [x] Mock PactDb implementation
- [ ] ChainwebPactDb implementation
- [x] implemented
- [ ] Gas

### write

- [x] Local Bypass Check (NOTBYPASSED)
- [x] Enforcing blessed hashes
- [x] Guarded db access (Module admin or calledByModule)
- [x] Mock PactDb implementation
- [ ] ChainwebPactDb implementation
- [x] implemented
- [ ] Gas

## Time Builtins

### add-time

- [x] implemented both overloads
- [ ] Gas

### days

- [x] implemented both overloads
- [ ] Gas

### diff-time

- [x] implemented both overloads
- [ ] Gas

### format-time

- [x] implemented
- [ ] Gas

### hours

- [x] implemented both overloads
- [ ] Gas

### minutes

- [x] implemented both overloads
- [ ] Gas

### parse-time

- [x] implemented
- [ ] Gas

### time

- [x] implemented
- [ ] Gas

## Operator Builtins

### !=

- [x] implemented
- [ ] Gas

### &

- [x] implemented
- [ ] Gas

### *

- [x] implemented integer case
- [x] implemented decimal case
- [ ] Gas

### +

- [x] implemented integer case
- [x] implemented decimal case
- [x] implemented string case (concatenation)
- [x] implemented object case (union)
- [ ] Gas

### -

- [x] implement - as negate (1-arg) for integer
- [x] implement - as negate (1-arg) for decimal
- [x] implement - as subtract (2-arg) for integer
- [x] implement - as subtract (2-arg) for decimal
- [x] implemented object case (union)
- [ ] Gas

### <

- [x] implemented integer case
- [x] implemented decimal case
- [x] implemented string case
- [x] implemented time case
- [ ] Gas

### <=

- [x] implemented integer case
- [x] implemented decimal case
- [x] implemented string case
- [x] implemented time case
- [ ] Gas

### =

- [x] implemented integer case
- [x] implemented decimal case
- [x] implemented string case
- [x] implemented bool case
- [x] implemented object case
- [x] implemented time case
- [x] implemented list case
- [x] implemented modref case
- [x] implemented guard case
- [ ] Gas

### >

- [x] implemented integer case
- [x] implemented decimal case
- [x] implemented string case
- [x] implemented time case
- [ ] Gas

### > =

- [x] implemented integer case
- [x] implemented decimal case
- [x] implemented string case
- [x] implemented time case
- [ ] Gas

### ^

- [x] implemented integer case
- [x] implemented decimal case
- [x] Musl
- [ ] Gas

### abs

- [x] implemented integer case
- [x] implemented decimal case
- [ ] Gas

### and

- [x] implemented with lazy eval
- [ ] Gas

### and?

- [x] implemented with lazy eval
- [ ] Gas

### ceiling

- [x] implemented base case
- [x] implemented specific precision case
- [ ] Gas

### dec

- [x] implemented
- [ ] Gas

### exp

- [x] implemented integer case
- [x] implemented decimal case
- [x] Musl
- [ ] Gas

### floor

- [x] implemented base case
- [x] implemented specific precision case
- [ ] Gas

### ln

- [x] implemented integer case
- [x] implemented decimal case
- [x] Musl
- [ ] Gas

### log

- [x] implemented integer case
- [x] implemented decimal case
- [x] Musl
- [ ] Gas

### mod

- [x] implemented integer case
- [ ] Gas

### not

- [x] implemented
- [ ] Gas

### not?

- [x] implemented
- [ ] Gas

### or

- [x] implemented with lazy eval
- [ ] Gas

### or?

- [x] implemented with lazy eval
- [ ] Gas

### round

- [x] implemented base case
- [x] implemented specific precision case
- [ ] Gas

### shift

- [x] implemented
- [ ] Gas

### sqrt

- [x] implemented integer case
- [x] implemented decimal case
- [x] Musl
- [ ] Gas

### xor

- [x] implemented
- [ ] Gas

### | (bitwise or)

- [x] implemented
- [ ] Gas

### | (bitwise not)

- [x] implemented
- [ ] Gas

## Keyset builtins

### define-keyset

- [x] Enforced top level only
- [x] implemented 2-arg case
- [x] implemented 1-arg case
- [x] namespaced
- [ ] Gas

### enforce-keyset

- [x] implemented guard case
- [x] implemented keyset name case
- [ ] Gas

### enforce-keyset

- [x] implemented guard case
- [x] implemented keyset name case
- [ ] Gas

### keys-2, keys-all, keys-any

TODO: do we need this as a native?

### read-keyset

- [x] implemented guard case
- [x] implemented keyset name case
- [ ] Gas

## Capability Builtins

### compose-capability

- [x] implemented
- [ ] Gas

### emit-event

- [x] implemented
- [ ] Gas

### enforce-guard

- [x] implemented (Same as enforce-keyset, basically they're an alias)
- [ ] Gas

### install-capability

- [x] implemented
- [ ] Gas

### require-capability

- [x] implemented
- [ ] Gas

### with-capability

- [x] implemented
- [ ] Gas

## SPV Builtins

### verify-spv

- [ ] implemented
- [ ] Gas

## Commitment builtins

### decrypt-cc20p1305

TODO: do we want this in core? Can we delete?

- [ ] implemented
- [ ] gas

### validate-keypair

TODO: do we want this in core? Can we delete?

- [ ] implemented
- [ ] gas

## Guard Builtins

### create-capability-guard

- [x] implemented
- [ ] Gas

### create-module-guard

- [x] implemented
- [ ] Gas

### create-pact-guard

- [x] implemented
- [ ] Gas

### create-principal

- [x] implemented
- [ ] Gas

### create-user-guard

- [x] implemented
- [x] executed as sys only
- [ ] Gas

## is-principal

- [x] implemented
- [ ] Gas

## keyset-ref-guard

- [x] implemented
- [ ] Gas

## typeof-principal

- [x] implemented
- [ ] Gas

## validate-principal

- [x] implemented
- [ ] Gas

## Zk Builtins

## pairing-check

- [x] implemented
- [x] ensure points that are tested are on the curve
- [ ] Gas

## point-add

- [x] implemented
- [x] ensure points that are tested are on the curve
- [ ] Gas

## scalar-mult

- [x] implemented
- [x] ensure points that are tested are on the curve
- [ ] Gas

## REPL-only Builtins

### begin-tx

- [x] implemented

### bench

- [ ] implemented

### commit-tx

- [x] implemented

### continue=-pact

- [x] implemented all 4 overloads

### env-data

- [ ] TODO: string case? Do we want to parse json still??? what is the use case vs just an object?
- [x] implemented object case

### env-dynref

TODO: may not be necessary with new fv

- [ ] implemented

### env-enable-repl-natives

- [ ] implemented

### env-entity

To be removed

### env-events

- [x] implemented

### env-exec-config

- [x] implemented

### env-gas

- [ ] implemented

### env-gaslimit

- [ ] implemented

### env-gaslog

- [ ] implemented

### env-gasmodel

- [ ] implemented

### env-gasprice

- [ ] implemented

### env-gasrate

- [ ] implemented

### env-hash

- [x] implemented

### env-keys

- [x] implemented

### env-namespace-policy

- [x] implemented

### env-sigs

- [x] implemented

### env-simulate-onchain

- [ ] This is a specific one related to error forking in pact. Likely we will implement it at a later date.

### expect

- [x] implemented

### expect-failure

- [x] implemented

### expect-that

- [x] implemented

### format-address

TODO: what are we doing about this?

### load

- [x] implemented

### mock-spv

- [ ] implemented

### pact-state

- [x] implemented 1-arg
- [x] implemented 2-arg

### print

- [x] implemented

### rollback-tx

- [x] implemented

### sig-keyset

- [x] implemented

### test-capability

- [x] implemented

### typecheck

- [ ] TODO: implement using new typed core

### verify

- [ ] implemented

### with-applied-env

DELETED. Unnecessary with core's arch.
