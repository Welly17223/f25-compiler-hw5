#ifndef CODEGEN_CODE_GENERATOR_H
#define CODEGEN_CODE_GENERATOR_H

#include "AST/ConstantValue.hpp"
#include "AST/FunctionInvocation.hpp"
#include "AST/VariableReference.hpp"
#include "AST/function.hpp"
#include "AST/operator.hpp"
#include "sema/SemanticAnalyzer.hpp"
#include "sema/SymbolTable.hpp"
#include "visitor/AstNodeVisitor.hpp"

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <stack>
#include <string>
#include <unordered_map>
#include <variant>

template <typename T> constexpr std::string_view type_name() {
#if defined(__clang__)
    return __PRETTY_FUNCTION__;
#elif defined(__GNUC__)
    return __PRETTY_FUNCTION__;
#elif defined(_MSC_VER)
    return __FUNCSIG__;
#else
    return "Unsupported compiler";
#endif
}

class CodeGenerator final : public AstNodeVisitor {
private:
    enum class CodeGenContext : uint8_t {
        kGlobal,
        kFunction,
        kForLoopIfWhile,
        kLocal
    };

public:
    struct Inst_virt_reg {
        bool true_inst;
        size_t write_reg;
        std::unique_ptr<std::vector<size_t>> read_regs;
        std::string inst;
    };
    enum class RiscvRegisterEnum : int8_t {
        NO_REG = -1,
        zero,
        ra,
        sp,
        gp,
        tp,
        t0,
        t1,
        t2,
        s0,
        s1,
        a0,
        a1,
        a2,
        a3,
        a4,
        a5,
        a6,
        a7,
        s2,
        s3,
        s4,
        s5,
        s6,
        s7,
        s8,
        s9,
        s10,
        s11,
        t3,
        t4,
        t5,
        t6,
    };

    class RiscvRegister {
    private:
        RiscvRegisterEnum reg;

    public:
        static const char *RegName[];
        static const uint8_t RegPriority[];
        const char *getNameCString() const { return RegName[(uint8_t)reg]; }
        friend bool operator<(const RiscvRegister &lhs,
                              const RiscvRegister &rhs) {
            return RegPriority[(uint8_t)lhs.reg] <
                   RegPriority[(uint8_t)rhs.reg];
        }
        friend bool operator>(const RiscvRegister &lhs,
                              const RiscvRegister &rhs) {
            return RegPriority[(uint8_t)lhs.reg] >
                   RegPriority[(uint8_t)rhs.reg];
        }
        friend bool operator==(const RiscvRegister &lhs,
                               const RiscvRegister &rhs) {
            return lhs.reg == rhs.reg;
        }
        friend bool operator!=(const RiscvRegister &lhs,
                               const RiscvRegister rhs) {
            return lhs.reg != rhs.reg;
        }
        const RiscvRegisterEnum operator()(RiscvRegisterEnum) { return reg; }
        RiscvRegister(RiscvRegisterEnum reg) : reg(reg) {}
        RiscvRegister() : reg((RiscvRegisterEnum)0) {}
        RiscvRegister(uint8_t reg) : RiscvRegister((RiscvRegisterEnum)reg) {}

        bool saved_callee() const {
            switch (reg) {
            case RiscvRegisterEnum::s1:
            case RiscvRegisterEnum::s2:
            case RiscvRegisterEnum::s3:
            case RiscvRegisterEnum::s4:
            case RiscvRegisterEnum::s5:
            case RiscvRegisterEnum::s6:
            case RiscvRegisterEnum::s7:
            case RiscvRegisterEnum::s8:
            case RiscvRegisterEnum::s9:
            case RiscvRegisterEnum::s10:
            case RiscvRegisterEnum::s11:
                return true;
            default:
                return false;
            }
        }

        bool saved_caller() const {
            switch (reg) {
            case RiscvRegisterEnum::t0:
            case RiscvRegisterEnum::t1:
            case RiscvRegisterEnum::t2:
            case RiscvRegisterEnum::t3:
            case RiscvRegisterEnum::t4:
            case RiscvRegisterEnum::t5:
            case RiscvRegisterEnum::t6:
            case RiscvRegisterEnum::a0:
            case RiscvRegisterEnum::a1:
            case RiscvRegisterEnum::a2:
            case RiscvRegisterEnum::a3:
            case RiscvRegisterEnum::a4:
            case RiscvRegisterEnum::a5:
            case RiscvRegisterEnum::a6:
            case RiscvRegisterEnum::a7:
                return true;
            default:
                return false;
            }
        }
    };

    struct ThreeAddressCodeOp {
        Operator op;
        size_t left, right;
    };
    using ThreeAddressCodeEntry =
        std::variant<ConstantValueNode *, VariableReferenceNode *,
                     FunctionInvocationNode *, ThreeAddressCodeOp>;

    // code could be Operator or other things
private:
    SymbolManager m_symbol_manager;
    std::stack<CodeGenContext> m_context_stack;
    std::stack<std::string> m_Inst_stack;
    std::stack<std::string> m_Inst_glob_stack;
    std::string m_Inst_buff;

    std::set<RiscvRegister> avaliable_reg;
    std::set<RiscvRegister> used_reg;
    std::vector<ThreeAddressCodeEntry> ThreeAddressCodeTable;
    std::vector<RiscvRegister> ThreeAddressCodeTableReg;

    std::string m_source_file_path;
    std::unordered_map<SemanticAnalyzer::AstNodeAddr, SymbolManager::Table>
        m_symbol_table_of_scoping_nodes;
    /// NOTE: `FILE` cannot be simply deleted by `delete`, so we need a custom
    /// deleter.
    std::unique_ptr<FILE, decltype(&fclose)> m_output_file{nullptr, &fclose};

    RiscvRegister expr_reg = 0;
    size_t three_addr_ind = 0;
    size_t current_sp = 0;
    size_t LocalConstantLabel = 0;
    size_t BranchLabel = 0;
    size_t function_arg_index = 0;

    void ResetAvaliableReg() {
        // Note: Avaliable register
        for (uint8_t i = 0; i < 32; i++) {
            auto reg = RiscvRegister(i);
            if (reg.saved_callee() ^ reg.saved_caller()) {
                avaliable_reg.emplace(std::move(reg));
            }
        }
        used_reg.clear();
    }

public:
    ~CodeGenerator() = default;
    CodeGenerator(
        const std::string &source_file_name, const std::string &save_path,
        std::unordered_map<SemanticAnalyzer::AstNodeAddr, SymbolManager::Table>
            &&p_symbol_table_of_scoping_nodes);

    RiscvRegister GetAvailableReg();
    void ReturnReg(RiscvRegister reg);

    SymbolEntry::KindEnum
    determineVarKind(const VariableNode &p_variable) const;
    bool isShadowingLoopVar(const std::string &p_name) const;
    bool isRedeclaringSymbol(const std::string &p_name) const;

    std::vector<CodeGenerator::RiscvRegister>
    expr_handler(size_t start_ind, RiscvRegister ret_reg);
    std::vector<CodeGenerator::RiscvRegister>
    expr_handler(size_t start_ind, RiscvRegister ret_reg,
                 std::string &inst_buf);

    void visit(ProgramNode &p_program) override;
    void visit(DeclNode &p_decl) override;
    void visit(VariableNode &p_variable) override;
    void visit(ConstantValueNode &p_constant_value) override;
    void visit(FunctionNode &p_function) override;
    void visit(CompoundStatementNode &p_compound_statement) override;
    void visit(PrintNode &p_print) override;
    void visit(BinaryOperatorNode &p_bin_op) override;
    void visit(UnaryOperatorNode &p_un_op) override;
    void visit(FunctionInvocationNode &p_func_invocation) override;
    void visit(VariableReferenceNode &p_variable_ref) override;
    void visit(AssignmentNode &p_assignment) override;
    void visit(ReadNode &p_read) override;
    void visit(IfNode &p_if) override;
    void visit(WhileNode &p_while) override;
    void visit(ForNode &p_for) override;
    void visit(ReturnNode &p_return) override;
};

#endif
