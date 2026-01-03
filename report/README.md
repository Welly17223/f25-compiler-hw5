# hw5 report

|||
|-:|:-|
|Name|yourname|
|許哲瑋|112550172|

## How much time did you spend on this project

> e.g. 2 hours.
60 hours

## Project overview

> Please describe the structure of your code and the ideas behind your implementation in an organized way.
> The point is to show us how you deal with the problems. It is not necessary to write a lot of words or paste all of your code here.
### 1. Overall Architecture
The code implements a **Backend Compiler** that translates an Abstract Syntax Tree (AST) into **RISC-V 32-bit assembly**. It utilizes the **Visitor Pattern** (`AstNodeVisitor`) to traverse the AST.

The generation process is divided into two distinct phases for expressions:
1.  **IR Generation:** Flattening the AST into a linear Intermediate Representation (Three-Address Code).
2.  **Assembly Emission:** converting IR to assembly using Register Allocation.

---

### 2. Handling Expressions: The Three-Address Code (TAC) Approach
Instead of generating assembly directly while traversing expression nodes (which causes register management headaches for nested expressions), the code uses a buffering strategy.

*   **Problem:** How to handle complex nested expressions like `a = (b + c) * (d - e)`?
*   **Solution:**
    *   The `visit` methods for expression nodes (`BinaryOperatorNode`, `ConstantValueNode`, etc.) do **not** print assembly immediately.
    *   Instead, they populate a `ThreeAddressCodeTable`. This table acts as a linear instruction buffer (Intermediate Representation).
    *   **Virtual Registers:** During this phase, operands are assigned temporary logical indices (virtual registers) rather than physical hardware registers.

### 3. Register Allocation Strategy
This is the most complex part of the implementation, found primarily in the `expr_handler` function. The goal is to map unlimited virtual registers to limited RISC-V physical registers.

*   **Algorithm:** The implementation uses a **Linear Scan-like** allocation strategy with Liveness Analysis.
*   **Steps:**
    1.  **Virtual Instruction Generation:** Convert the accumulated `ThreeAddressCodeTable` into `Inst_virt_reg` objects.
    2.  **Liveness Analysis:** Calculate **Live Ranges** (start and end points) for every virtual register. It iterates backward through instructions to compute `LiveIn` and `LiveOut` sets.
    3.  **Physical Assignment:** Iterate through live ranges. For each virtual register:
        *   Check which physical registers (`a0`-`a7`, `t0`-`t6`, `s1`-`s11`) are free during that specific time interval.
        *   Assign the first non-overlapping physical register.
    4.  **Spilling (Problem Solving):**
        *   If no physical register is available, the variable is **spilled** to the stack.
        *   **Reserved Registers:** Registers `t5` and `t6` are explicitly excluded from the general allocation pool (`ResetAvaliableReg`).
        *   When a spilled virtual register is read/written, the code generates `lw`/`sw` instructions using `t5` or `t6` as temporary scratchpads to move data between the stack and the CPU.

### 4. Stack and Memory Management
The compiler manually manages the stack frame for local variables and function calls.

*   **Stack Pointer (`sp`) Tracking:**
    *   A member variable `current_sp` tracks the current offset relative to the Frame Pointer (`s0`).
    *   When entering a scope (`CompoundStatement` or `Function`), `current_sp` is adjusted.
*   **Symbol Table Integration:**
    *   When a variable is declared (`visit(VariableNode)`), its offset is calculated based on its type size (4 bytes for int/float) and array dimensions.
    *   This offset is stored in the `SymbolEntry` (`setSp`). Future references (`VariableReferenceNode`) look up this offset to generate `lw/sw ... (s0)` instructions.
*   **Prologue/Epilogue:**
    *   `visit(FunctionNode)` generates the standard RISC-V prologue: Save Return Address (`ra`) and Frame Pointer (`s0`), then move `sp`.
    *   The epilogue restores these registers and jumps back (`jr ra`).

### 5. Control Flow (If, While, For)
Control flow requires jumping over blocks of code, which is handled via label generation.

*   **Label Management:** A counter `BranchLabel` ensures every jump target (`L1`, `L2`, etc.) is unique.
*   **Instruction Buffering (`m_Inst_buff`):**
    *   To handle loops and conditionals correctly, the generator often needs to construct the body of a loop before knowing the jump instruction size or exact offsets.
    *   The code uses string buffers (`m_Inst_buff`, `m_Inst_stack`) to build code blocks (condition calculation, loop body) and then concatenates them in the correct logical order (Condition -> Branch -> Body -> Jump Back).

### 6. Function Calls and ABI Compliance
The implementation adheres to the RISC-V Calling Convention.

*   **Caller-Saved vs. Callee-Saved:**
    *   The `RiscvRegister` class distinguishes between caller-saved (`t` registers) and callee-saved (`s` registers).
    *   During `expr_handler`, if a function call instruction is encountered within a live range, the allocator only assign **callee-saved** registers (`s1`-`s11`) or spill it to variables that live across the function call. This avoids the need to save/restore them around the `call`.
*   **Arguments:**
    *   The first 8 arguments are moved to `a0`-`a7`.
    *   Excess arguments are pushed onto the stack.

### Summary
The core philosophy of this implementation is to **decouple logical operations from hardware constraints** as much as possible:
1.  **AST** is flattened to **IR** (Logic).
2.  **IR** is analyzed for **Liveness** (Temporal Logic).
3.  **Physical Registers** are assigned, handling collisions via **Spilling** (Hardware Constraint).
## What is the hardest you think in this project

> Not required, but bonus point may be given.

## Feedback to T.A.s

> Not required, but bonus point may be given.
