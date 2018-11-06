IELE Textual Syntax
===================

Here we define the textual syntax of IELE assembly code. The syntax represented here has some syntactic sugar which is removed by the assembler. However, a fragment of this textual encoding is used by the semantics to express the rules of the language itself. The [iele-examples](iele-examples) directory contains various sample IELE contracts, such as:
* a [simple open auction contract](iele-examples/simpleOpenAuction.iele);
* an [ERC20 token](iele-examples/erc20.iele);  and
* a [forwarding wallet contract](iele-examples/forwardingWallet.iele).

The best way to understand the meaning of the IELE syntactic constructs is to read their actual formal semantics in [iele.md](iele.md).

Names and Literals
------------------

### IELE Names

IELE uses alphanumeric names for identifying registers, labels, functions, and contracts. IELE "keywords" are also valid identifiers.

```k
module IELE-SYNTAX
  imports IELE-COMMON

  syntax IeleName ::= r"(?<![A-Za-z0-9\\_\\.\\-\\$])[a-zA-Z\\.\\_\\$][0-9a-zA-Z\\.\\_\\-\\$]*" [token, notInRules, prec(3)]

  syntax Keyword ::= "load" | "store" | "sload"  | "sstore" | "iszero" | "not"  | "add"  | "mul"  | "sub" | "div"
                   | "exp"  | "mod"   | "addmod" | "mulmod" | "expmod" | "byte" | "sext" | "twos" | "and" | "or"
                   | "xor"  | "shift" | "lt"     | "le"     | "gt"     | "ge"   | "eq"   | "ne"   | "cmp" | "sha3"
  
  syntax Keyword ::= "br"   | "call"   | "staticcall" | "at" | "send"  | "gaslimit" | "ret"      | "void"   | "revert"
                   | "log"  | "create" | "copycreate" | "selfdestruct" | "contract" | "external" | "define" | "public"
                   | "log2" | "bswap"  | "calladdress"
  syntax IeleName ::= Keyword [token]

  syntax NumericIeleName ::= r"[0-9]+" [token]

  syntax StringIeleName ::= r"\\\"(([^\\\"\\\\])|(\\\\[0-9a-fA-F]{2}))*\\\"" [token]
endmodule
```

Local register names are desugared to integers when assembling an IELE program

```k
module IELE-COMMON
  imports DOMAINS-SYNTAX
  imports INT-SYNTAX
  syntax NumericIeleName ::= Int
  syntax StringIeleName
  syntax IeleName ::= NumericIeleName
  syntax IeleName ::= StringIeleName [klabel(StringIeleName), avoid, symbol]
```

### Identifiers

IELE has two categories of identifiers: local and global names.

-   Local names have function-wide scope, are used for naming registers, and begin with `%`.
-   Global names have contract-wide scope, are used for naming globals and functions, and begin with `@`.

```k
  syntax GlobalName ::= "@" IeleName

  syntax LocalName ::= "%" IeleName

  syntax LocalNames ::= List{LocalName, ","} [klabel(localNameList)]
```

### Constants

-   IELE constants include unbounded signed integer literals and globals.
-   IELE globals serve as names with contract-wide scope that hold a constant value (cannot be modified).

```k
  syntax Constant ::= IntConstant | GlobalName
  syntax IntConstant ::= Int | Bool | HexConstant
  syntax HexConstant ::= r"0x[0-9a-fA-F]+" [token]
```

Instructions
------------

### Operands

IELE instruction operands are used at the left- and right-hand side of IELE instructions.

-   One or more `LValues` can be used at the left-hand side of various IELE instructions
-   Zero or more `Operands` can be used at the right-hand side of various IELE instructions and as actual argument lists in function calls.
-   Constants can only be used as right-hand side operands, while registers can be used as both left- and right-hand side operands.
-   Each right-hand side operand will be heated to an unbounded signed integer value during execution.

```k
  syntax LValue ::= LocalName
  
  syntax LValues ::= NeList{LValue, ","} [klabel(lvalueList)]

  syntax Operand ::= LValue | Constant

  syntax Operands ::= List{Operand, ","} [klabel(operandList)]

  syntax NonEmptyOperands ::= NeList{Operand, ","} [klabel(operandList)]

  syntax Ints ::= List{Int, ","} [klabel(operandList)]

  syntax Operands ::= Ints
```

### Assignment

Simple copy assignment that loads a value into a register.

```k
  syntax AssignInst ::= LValue "=" Operand
```

### Local Memory

Instructions that provide access to the local execution memory. For more details see [here](Design.md#local-execution-memory).

```k
  syntax LoadInst ::= LValue "=" "load" /* cell */ Operand [strict(2)]
  syntax LoadInst ::= LValue "=" "load" /* cell */ Operand "," /* offset in bytes */ Operand "," /* width in bytes */ Operand [seqstrict(2,3,4)]
  syntax StoreInst ::= "store" /* value */ Operand "," /* cell */ Operand [seqstrict(1,2)]
  syntax StoreInst ::= "store" /* value */ Operand "," /* cell */ Operand "," /* offset in bytes */ Operand "," /* width in bytes */ Operand [seqstrict(1,2,3,4)]
```

### Account Storage

Instructions that provide access to the account storage. For more details see [here](Design.md#account-storage).

```k
  syntax SLoadInst ::= LValue "=" "sload" /* index */ Operand [strict(2)]
  syntax SStoreInst ::= "sstore" /* value */ Operand "," /* index */ Operand [seqstrict(1,2)]
```

### Expressions

Various expressions over unbounded signed integers. For more details see [here](Design.md#arbitrary-precision-words).

```k
  syntax IsZeroInst ::= LValue "=" "iszero" Operand [strict(2)]
  syntax NotInst    ::= LValue "=" "not"    Operand [strict(2)]

  syntax AddInst ::= LValue "=" "add" Operand "," Operand [seqstrict(2,3)]
  syntax MulInst ::= LValue "=" "mul" Operand "," Operand [seqstrict(2,3)]
  syntax SubInst ::= LValue "=" "sub" Operand "," Operand [seqstrict(2,3)]
  syntax DivInst ::= LValue "=" "div" Operand "," Operand [seqstrict(2,3)]
  syntax ExpInst ::= LValue "=" "exp" Operand "," Operand [seqstrict(2,3)]
  syntax ModInst ::= LValue "=" "mod" Operand "," Operand [seqstrict(2,3)]

  syntax AddModInst ::= LValue "=" "addmod" Operand "," Operand "," Operand [seqstrict(2,3,4)]
  syntax MulModInst ::= LValue "=" "mulmod" Operand "," Operand "," Operand [seqstrict(2,3,4)]
  syntax ExpModInst ::= LValue "=" "expmod" Operand "," Operand "," Operand [seqstrict(2,3,4)]

  syntax LogInst   ::= LValue "=" "log2"                                    Operand             [strict(2)]
  syntax ByteInst  ::= LValue "=" "byte"  /* byte index, 0 being the LSB */ Operand "," Operand [seqstrict(2,3)]
  syntax SExtInst  ::= LValue "=" "sext"  /* width in bytes */              Operand "," Operand [seqstrict(2,3)]
  syntax TwosInst  ::= LValue "=" "twos"  /* width in bytes */              Operand "," Operand [seqstrict(2,3)]
  syntax BswapInst ::= LValue "=" "bswap" /* width in bytes */              Operand "," Operand [seqstrict(2,3)]

  syntax AndInst   ::= LValue "=" "and"   Operand "," Operand [seqstrict(2,3)]
  syntax OrInst    ::= LValue "=" "or"    Operand "," Operand [seqstrict(2,3)]
  syntax XorInst   ::= LValue "=" "xor"   Operand "," Operand [seqstrict(2,3)]
  syntax ShiftInst ::= LValue "=" "shift" Operand "," /* shift amount */ Operand [seqstrict(2,3)]

  syntax Predicate ::= "lt" | "le" | "gt" | "ge" | "eq" | "ne"
  syntax CmpInst ::= LValue "=" "cmp" Predicate Operand "," Operand [seqstrict(3,4)]

  syntax SHA3Inst ::= LValue "=" "sha3" Operand [strict(2)]
```

### Static Jumps

Instructions for conditional and unconditional jumps within the function's body. For more details see [here](Design.md#static-jumps).

```k
  syntax JumpInst     ::= "br" IeleName
  syntax CondJumpInst ::= "br" Operand "," IeleName [strict(1)]
```

### Function Calls and Returns

Instructions for local functions calls to other functions of the same contract, as well as contract function calls to public functions of contracts deployed in other accounts. For more details see [here](Design.md#function-callreturn).

```k
  syntax LocalCallInst   ::= "call" Operand "(" Operands ")"
                           | LValues "=" "call" Operand "(" Operands ")" [strict(2,3)]
  syntax AccountCallInst ::= LValues "=" "call" Operand "at" Operand "(" Operands ")" "send" Operand "," "gaslimit" Operand [seqstrict(2,3,4,5,6)]
  syntax AccountCallInst ::= LValues "=" "staticcall" Operand "at" Operand "(" Operands ")" "gaslimit" Operand [seqstrict(2,3,4,5)]

  syntax CallAddressInst ::= LValue "=" "calladdress" GlobalName "at" Operand [strict(3)]

  syntax ReturnInst ::= "ret" NonEmptyOperands [strict(1)]
                      | "ret" "void"
  syntax RevertInst ::= "revert" Operand [strict(1)]
```

### Logging

Instructions to append information to the substate log. These variations append the entire content of a local execution memory cell to the log along with zero to four log topics.

```k
  syntax LogInst ::= "log" /* cell */ Operand [strict(1)]
                   | "log" /* cell */ Operand "," NonEmptyOperands [seqstrict(1,2)]
```

### Account Creation and Deletion

Instructions to create and/or delete a new account with a contract deployed with it. For more details see [here](Design.md#contract-creation).

```k
  syntax CreateInst ::= /* exit status */ LValue "," /* new account address */ LValue "=" "create"     /* contract name */    IeleName "(" Operands ")" "send" Operand [seqstrict(4,5)]
  syntax CreateInst ::= /* exit status */ LValue "," /* new account address */ LValue "=" "copycreate" /* contract address */ Operand  "(" Operands ")" "send" Operand [seqstrict(3,4,5)]

  syntax SelfdestructInst ::= "selfdestruct" /* account to send balance */ Operand [strict(1)]
````

Hybrid attribute desugaring
============================

```k
  syntax LoadedLoadInst ::= LValue "=" "load" Constant
  syntax LoadedLoadInst ::= LValue "=" "load" Constant "," Constant "," Constant
  syntax KResult ::= LoadedLoadInst
  syntax LoadInst ::= LoadedLoadInst

  syntax LoadedStoreInst ::= "store" Constant "," Constant
  syntax LoadedStoreInst ::= "store" Constant "," Constant "," Constant "," Constant
  syntax KResult ::= LoadedStoreInst
  syntax StoreInst ::= LoadedStoreInst

  syntax LoadedSLoadInst ::= LValue "=" "sload" Constant
  syntax KResult ::= LoadedSLoadInst
  syntax SLoadInst ::= LoadedSLoadInst

  syntax LoadedSStoreInst ::= "sstore" Constant "," Constant
  syntax KResult ::= LoadedSStoreInst
  syntax SStoreInst ::= LoadedSStoreInst

  syntax LoadedIsZeroInst ::= LValue "=" "iszero" Constant
  syntax KResult ::= LoadedIsZeroInst
  syntax IsZeroInst ::= LoadedIsZeroInst

  syntax LoadedNotInst    ::= LValue "=" "not" Constant
  syntax KResult ::= LoadedNotInst
  syntax NotInst ::= LoadedNotInst

  syntax LoadedAddInst ::= LValue "=" "add" Constant "," Constant
  syntax KResult ::= LoadedAddInst
  syntax AddInst ::= LoadedAddInst

  syntax LoadedMulInst ::= LValue "=" "mul" Constant "," Constant
  syntax KResult ::= LoadedMulInst
  syntax MulInst ::= LoadedMulInst

  syntax LoadedSubInst ::= LValue "=" "sub" Constant "," Constant
  syntax KResult ::= LoadedSubInst
  syntax SubInst ::= LoadedSubInst

  syntax LoadedDivInst ::= LValue "=" "div" Constant "," Constant
  syntax KResult ::= LoadedDivInst
  syntax DivInst ::= LoadedDivInst

  syntax LoadedExpInst ::= LValue "=" "exp" Constant "," Constant
  syntax KResult ::= LoadedExpInst
  syntax ExpInst ::= LoadedExpInst

  syntax LoadedModInst ::= LValue "=" "mod" Constant "," Constant
  syntax KResult ::= LoadedModInst
  syntax ModInst ::= LoadedModInst

  syntax LoadedAddModInst ::= LValue "=" "addmod" Constant "," Constant "," Constant
  syntax KResult ::= LoadedAddModInst
  syntax AddModInst ::= LoadedAddModInst

  syntax LoadedMulModInst ::= LValue "=" "mulmod" Constant "," Constant "," Constant
  syntax KResult ::= LoadedMulModInst
  syntax MulModInst ::= LoadedMulModInst

  syntax LoadedExpModInst ::= LValue "=" "expmod" Constant "," Constant "," Constant
  syntax KResult ::= LoadedExpModInst
  syntax ExpModInst ::= LoadedExpModInst

  syntax LoadedLogInst   ::= LValue "=" "log2"  Constant
  syntax KResult ::= LoadedLogInst
  syntax LogInst ::= LoadedLogInst

  syntax LoadedByteInst  ::= LValue "=" "byte"  Constant "," Constant
  syntax KResult ::= LoadedByteInst
  syntax ByteInst ::= LoadedByteInst

  syntax LoadedSExtInst  ::= LValue "=" "sext"  Constant "," Constant
  syntax KResult ::= LoadedSExtInst
  syntax SExtInst ::= LoadedSExtInst

  syntax LoadedTwosInst  ::= LValue "=" "twos"  Constant "," Constant
  syntax KResult ::= LoadedTwosInst
  syntax TwosInst ::= LoadedTwosInst

  syntax LoadedBswapInst ::= LValue "=" "bswap" Constant "," Constant
  syntax KResult ::= LoadedBswapInst
  syntax BswapInst ::= LoadedBswapInst

  syntax LoadedAndInst   ::= LValue "=" "and"   Constant "," Constant
  syntax KResult ::= LoadedAndInst
  syntax AndInst ::= LoadedAndInst

  syntax LoadedOrInst    ::= LValue "=" "or"    Constant "," Constant
  syntax KResult ::= LoadedOrInst
  syntax OrInst ::= LoadedOrInst

  syntax LoadedXorInst   ::= LValue "=" "xor"   Constant "," Constant
  syntax KResult ::= LoadedXorInst
  syntax XorInst ::= LoadedXorInst

  syntax LoadedShiftInst ::= LValue "=" "shift" Constant "," Constant
  syntax KResult ::= LoadedShiftInst
  syntax ShiftInst ::= LoadedShiftInst

  syntax LoadedCmpInst ::= LValue "=" "cmp" Predicate Constant "," Constant
  syntax KResult ::= LoadedCmpInst
  syntax CmpInst ::= LoadedCmpInst

  syntax LoadedSHA3Inst ::= LValue "=" "sha3" Constant
  syntax KResult ::= LoadedSHA3Inst
  syntax SHA3Inst ::= LoadedSHA3Inst

  syntax LoadedCondJumpInst ::= "br" Constant "," IeleName
  syntax KResult ::= LoadedCondJumpInst
  syntax CondJumpInst ::= LoadedCondJumpInst

  syntax LoadedLocalCallInst   ::= LValues "=" "call" Constant "(" Ints ")"
  syntax KResult ::= LoadedLocalCallInst
  syntax LocalCallInst ::= LoadedLocalCallInst

  syntax LoadedAccountCallInst ::= LValues "=" "call" Constant "at" Constant "(" Ints ")" "send" Constant "," "gaslimit" Constant
  syntax LoadedAccountCallInst ::= LValues "=" "staticcall" Constant "at" Constant "(" Ints ")" "gaslimit" Constant
  syntax KResult ::= LoadedAccountCallInst
  syntax AccountCallInst ::= LoadedAccountCallInst

  syntax LoadedCallAddressInst ::= LValue "=" "calladdress" GlobalName "at" Constant
  syntax KResult ::= LoadedCallAddressInst
  syntax CallAddressInst ::= LoadedCallAddressInst

  syntax LoadedReturnInst ::= "ret" Ints
  syntax KResult ::= LoadedReturnInst
  syntax ReturnInst ::= LoadedReturnInst

  syntax LoadedRevertInst ::= "revert" Constant
  syntax KResult ::= LoadedRevertInst
  syntax RevertInst ::= LoadedRevertInst

  syntax LoadedLogInst ::= "log" Constant
                         | "log" Constant "," Ints
  syntax KResult ::= LoadedLogInst
  syntax LogInst ::= LoadedLogInst

  syntax LoadedCreateInst ::= LValue "," LValue "=" "create"     IeleName "(" Ints ")" "send" Constant
  syntax LoadedCreateInst ::= LValue "," LValue "=" "copycreate" Constant "(" Ints ")" "send" Constant
  syntax KResult ::= LoadedCreateInst
  syntax CreateInst ::= LoadedCreateInst

  syntax LoadedSelfdestructInst ::= "selfdestruct" Constant
  syntax KResult ::= LoadedSelfdestructInst
  syntax SelfdestructInst ::= LoadedSelfdestructInst

```

### Local and Network State Accessors

These accessors are implemented as builtins that can be called using the same syntax as in a local call, e.g. `%pc = call @iele.pc()` or `%balance = call @iele.balance(%bank.account)`. The names of the builtins follow the IELE convention for intrinsics: Their name is a valid global name that starts with the prefix `iele.`. This means that no user-defined global name can start with the prefix `iele.`.

```k
  syntax IeleName ::= "iele.invalid"     [token]
  // local state queries
  syntax IeleName ::= "iele.gas"         [token]
  syntax IeleName ::= "iele.gasprice"    [token]
  syntax IeleName ::= "iele.gaslimit"    [token]
  syntax IeleName ::= "iele.beneficiary" [token]
  syntax IeleName ::= "iele.timestamp"   [token]
  syntax IeleName ::= "iele.number"      [token]
  syntax IeleName ::= "iele.difficulty"  [token]
  syntax IeleName ::= "iele.address"     [token]
  syntax IeleName ::= "iele.origin"      [token]
  syntax IeleName ::= "iele.caller"      [token]
  syntax IeleName ::= "iele.callvalue"   [token]
  syntax IeleName ::= "iele.msize"       [token]
  syntax IeleName ::= "iele.codesize"    [token]
  syntax IeleName ::= "iele.blockhash"   [token]
  // account queries
  syntax IeleName ::= "iele.balance"     [token]
  syntax IeleName ::= "iele.extcodesize" [token]
```

### Precompiled Contracts

Precompiled contracts are also available as IELE builtins but they should be called using the syntax for an account call targeting the account with address `1` (e.g. `%res  = call @iele.sha256 at 1 ( %len, %data ) send %val, gaslimit %gas`).

```k
  syntax IeleName ::= "iele.ecrec"     [token]
  syntax IeleName ::= "iele.sha256"    [token]
  syntax IeleName ::= "iele.rip160"    [token]
  syntax IeleName ::= "iele.id"        [token]
  syntax IeleName ::= "iele.ecadd"     [token]
  syntax IeleName ::= "iele.ecmul"     [token]
  syntax IeleName ::= "iele.ecpairing" [token]
```

#### Instruction Lists

```k
  syntax Instruction ::=
    AssignInst
  | LoadInst
  | StoreInst
  | SLoadInst
  | SStoreInst
  | IsZeroInst
  | NotInst
  | AddInst
  | MulInst
  | SubInst
  | DivInst
  | ExpInst
  | ModInst
  | AddModInst
  | MulModInst
  | ExpModInst
  | ByteInst
  | SExtInst
  | TwosInst
  | BswapInst
  | AndInst
  | OrInst
  | XorInst
  | ShiftInst
  | CmpInst
  | SHA3Inst
  | JumpInst
  | CondJumpInst
  | LocalCallInst
  | AccountCallInst
  | CallAddressInst
  | ReturnInst
  | RevertInst
  | LogInst
  | CreateInst
  | SelfdestructInst

  syntax Instructions ::= List{Instruction, ""} [klabel(instructionList), format(%1%2%n%3)]
```

IELE Program Structure
----------------------

### Contracts

A contract is a compilation unit of code to be deployed with an account in the blockchain.

-   A IELE program consists of a list of one or more contracts.
-   The last contract in the list is the main contract.
-   Each contract has a name and consists of a list of top-level definitions.
-   Top-level definitions include external contract declarations, global definitions, and function definitions.

For more details see below and [here](Design.md#program-structure).

```k
  syntax TopLevelDefinition ::=
    FunctionDefinition
  | GlobalDefinition
  | ContractDeclaration

  syntax TopLevelDefinitions ::= List{TopLevelDefinition, ""} [klabel(topLevelDefinitionList), format(%1%2%n%3)]

  syntax ContractDefinition ::= "contract" IeleName "{" TopLevelDefinitions "}" [format(%1 %2 %3%n%i%4%d%n%5)]

  syntax Contract ::= List{ContractDefinition, ""} [klabel(contractDefinitionList)]
```

### Contract declarations

A contract can only create accounts with deployed contracts that have been externaly declared within its top-level. A corresponding contract definition for each external contract declaration should precede this contract definition. This design decision ensures that a contract can only create new accounts with deployed contracts for which the code is available to it.

```k
  syntax ContractDeclaration ::= "external" "contract" IeleName
```

### Global Registers

Definition of globals and their constant values. Globals are accessible from within any function of the contract and their value cannot be modified.

```k
  syntax GlobalDefinition ::= GlobalName "=" IntConstant  [klabel(globalDefinition)]
```

### Functions

Function definitions consist of a function signature (function name and names of formal arguments) and a function body (a list of blocks containing the code of the function). Functions can be defined as `public` meaning that they can be called from a contract deployed with another account. Non-`public` functions can only be called locally within the contract.

```k
  syntax FunctionSignature ::= GlobalName "(" FunctionParameters ")"

  syntax FunctionParameters ::= LocalNames

  syntax FunctionDefinition ::= 
    "define" FunctionSignature "{" Blocks "}"             [format(%1 %2 %3%i%n%4%d%n%5%n)]
  | "define" "public" FunctionSignature "{" Blocks "}" [format(%1 %2 %3 %4%i%n%5%d%n%6%n)]
```

### Blocks

The body of a function is a list of blocks, where each block is a list of IELE instructions. Each block except the first one has to be preceded by a label, making the first instruction of the block a valid target of a local jump. The first block can also be optionally labeled.

```k
  syntax LabeledBlock ::= IeleName ":" Instructions

  syntax LabeledBlocks ::= List{LabeledBlock, ""} [klabel(labeledBlockList)]

  syntax UnlabeledBlock ::= Instructions

  syntax Blocks [flatPredicate]
  syntax Blocks ::= UnlabeledBlock LabeledBlocks [avoid] | LabeledBlocks
```

### Reserved IELE Function Names

-   An account to which code has never been deployed contains an implicit contract with one public function named `@deposit` which takes no arguments, returns no values, and does nothing. This function exists to allow such accounts to receive payments.
-   A special private function named `@init` should be defined for every contract and will be called when an account is created with this contract.

```k
  syntax IeleName ::= "deposit" [token]

  syntax IeleName ::= "init" [token]
```

#### Macros

Finally, following are macros for desugaring empty `LValues` and `Operands` lists in calls and returns.

```k
  rule call NAME ( ARGS ) => .LValues = call NAME ( ARGS ) [alias]
  rule ret void => ret .NonEmptyOperands [alias]
endmodule
```

