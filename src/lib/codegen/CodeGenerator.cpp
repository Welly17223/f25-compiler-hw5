#include "codegen/CodeGenerator.hpp"
#include "AST/CompoundStatement.hpp"
#include "AST/ConstantValue.hpp"
#include "AST/FunctionInvocation.hpp"
#include "AST/VariableReference.hpp"
#include "AST/decl.hpp"
#include "AST/for.hpp"
#include "AST/function.hpp"
#include "AST/operator.hpp"
#include "AST/program.hpp"
#include "sema/SemanticAnalyzer.hpp"
#include "sema/SymbolTable.hpp"
#include "visitor/AstNodeInclude.hpp"

#include <algorithm>
#include <cassert>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <iostream>
#include <iterator>
#include <memory>
#include <pstl/glue_execution_defs.h>
#include <string>
#include <sys/types.h>
#include <type_traits>
#include <unordered_map>
#include <utility>

#include <execution>
#include <numeric>
#include <vector>

#define INT_SIZE (4)
#define FLOAT_SIZE (4)

const char *CodeGenerator::RiscvRegister::RegName[] = {
    "zero", "ra", "sp", "gp", "tp",  "t0",  "t1", "t2", "s0", "s1", "a0",
    "a1",   "a2", "a3", "a4", "a5",  "a6",  "a7", "s2", "s3", "s4", "s5",
    "s6",   "s7", "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6",
};

const uint8_t CodeGenerator::RiscvRegister::RegPriority[] = {
    32, 32, 32, 32, 32, 0,  1,  2,  12, 13, 14, 25, 26, 11, 10, 9,
    8,  7,  15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 3,  4,  5,  6,
};

namespace {
const CodeGenerator::RiscvRegister ArgumentRegisters[] = {
    CodeGenerator::RiscvRegisterEnum::a0, CodeGenerator::RiscvRegisterEnum::a1,
    CodeGenerator::RiscvRegisterEnum::a2, CodeGenerator::RiscvRegisterEnum::a3,
    CodeGenerator::RiscvRegisterEnum::a4, CodeGenerator::RiscvRegisterEnum::a5,
    CodeGenerator::RiscvRegisterEnum::a6, CodeGenerator::RiscvRegisterEnum::a7,
};
}

template <class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
template <class... Ts> overloaded(Ts...) -> overloaded<Ts...>;

constexpr const char *const riscv_assembly_add_stack_pointer =
    "\taddi sp, sp, -%ld\n";
constexpr const char *const riscv_assembly_reset_stack_pointer =
    "\taddi sp, sp, %ld\n";
constexpr const char *const riscv_assembly_sw = "\taddi sp, sp, -4\n"
                                                "\tsw %s, %d(%s)\n";
constexpr const char *const riscv_assembly_lw = "\taddi sp, sp, 4\n"
                                                "\tlw %s, %d(%s)\n";
constexpr const char *const riscv_assmbly_load_constant_integer =
    "\tli %s, %s\n";
constexpr const char *const riscv_assembly_load_global =
    "\tla %s, %s\t\t\t\t# load global variable address %s\n"
    "\tlw %s, %d(%s)\n";
constexpr const char *const riscv_assembly_load_local =
    "\tlw %s, %ld(s0)\t\t\t# load local variable %s\n";
constexpr const char *const riscv_assembly_op =
    "\t%s %s, %s, %s\t\t\t# op reg1, reg1, reg2\n";

CodeGenerator::CodeGenerator(
    const std::string &source_file_name, const std::string &save_path,
    std::unordered_map<SemanticAnalyzer::AstNodeAddr, SymbolManager::Table>
        &&p_symbol_table_of_scoping_nodes)
    : m_symbol_manager(false /* no dump */),
      m_source_file_path(source_file_name),
      m_symbol_table_of_scoping_nodes(
          std::move(p_symbol_table_of_scoping_nodes)) {
    // FIXME: assume that the source file is always xxxx.p
    const auto &real_path = save_path.empty() ? std::string{"."} : save_path;
    auto slash_pos = source_file_name.rfind('/');
    auto dot_pos = source_file_name.rfind('.');

    if (slash_pos != std::string::npos) {
        ++slash_pos;
    } else {
        slash_pos = 0;
    }
    auto output_file_path{
        real_path + "/" +
        source_file_name.substr(slash_pos, dot_pos - slash_pos) + ".S"};
    m_output_file.reset(fopen(output_file_path.c_str(), "w"));
    assert(m_output_file.get() && "Failed to open output file");

    // Note: Avaliable register
    ResetAvaliableReg();
}

static void dumpInstructions(FILE *p_out_file, const char *format, ...) {
    va_list args;
    va_start(args, format);
    vfprintf(p_out_file, format, args);
    va_end(args);
}

SymbolEntry::KindEnum
CodeGenerator::determineVarKind(const VariableNode &p_variable) const {
    if (m_context_stack.top() == CodeGenContext::kForLoop) {
        return SymbolEntry::KindEnum::kLoopVarKind;
    }

    if (m_context_stack.top() == CodeGenContext::kFunction) {
        return SymbolEntry::KindEnum::kParameterKind;
    }

    // global or local
    return p_variable.getConstantPtr() ? SymbolEntry::KindEnum::kConstantKind
                                       : SymbolEntry::KindEnum::kVariableKind;
}

// NOTE: An anonymous namespace is used to define a function that is only
// visible in the current translation unit, which is similar to the static
// keyword in C.
namespace {
bool hasNonPositiveDimension(const PType *p_type) {
    return std::any_of(p_type->getDimensions().begin(),
                       p_type->getDimensions().end(),
                       [](const int dim) { return dim <= 0; });
}
} // namespace

bool CodeGenerator::isShadowingLoopVar(const std::string &p_name) const {
    auto to_be_shadowed = m_symbol_manager.lookup(p_name);
    return to_be_shadowed &&
           to_be_shadowed->getKind() == SymbolEntry::KindEnum::kLoopVarKind;
}

bool CodeGenerator::isRedeclaringSymbol(const std::string &p_name) const {
    return m_symbol_manager.getCurrentTable()->lookup(p_name);
}

CodeGenerator::RiscvRegister CodeGenerator::GetAvailableReg() {
    auto reg = *avaliable_reg.begin();
    avaliable_reg.erase(reg);
    if (reg.saved_callee()) {
        dumpInstructions(m_output_file.get(), riscv_assembly_sw,
                         reg.getNameCString(), 0LU, "sp");
    }
    fprintf(stderr, "used: %s\n", reg.getNameCString());
    return reg;
}

void CodeGenerator::ReturnReg(RiscvRegister reg) {
    if (reg == RiscvRegisterEnum::zero)
        return;
    if (reg.saved_callee()) {
        dumpInstructions(m_output_file.get(), riscv_assembly_lw,
                         reg.getNameCString(), 0LU, "sp");
    }
    used_reg.erase(reg);
    avaliable_reg.insert(reg);
    fprintf(stderr, "return: %s\n", reg.getNameCString());
}

std::vector<CodeGenerator::RiscvRegister>
CodeGenerator::expr_handler(size_t start_ind, RiscvRegister ret_reg) {
    std::vector<RiscvRegister> local_used_reg(ThreeAddressCodeTable.size());
    auto localThreeAddressCodeTable = std::move(ThreeAddressCodeTable);

    if (ret_reg != RiscvRegisterEnum::zero) {
        local_used_reg[start_ind] = ret_reg;
        used_reg.emplace(ret_reg);
        avaliable_reg.erase(ret_reg);
    }

    std::unordered_map<std::string, RiscvRegister> var_ref_regs;
    std::stack<std::string> inst_stack;

    fprintf(stderr, "start expr_handler: \n");
    int ind = start_ind;
    std::for_each(
        localThreeAddressCodeTable.begin() + start_ind,
        localThreeAddressCodeTable.end(), [&](const auto &e) {
            RiscvRegister &p_expr_reg = local_used_reg[ind];
            bool dump_inst = true;
            char inst_buf_c_str[1024];
            std::string pre_inst_buf, post_inst_buf;

            std::visit(
                overloaded{
                    [&](VariableReferenceNode *arg) {
                        if (var_ref_regs.count(arg->getNameCString())) {
                            p_expr_reg = var_ref_regs[arg->getNameCString()];
                            dump_inst = false;
                        } else if (p_expr_reg == 0) {
                            auto avaliable_reg = GetAvailableReg();
                            p_expr_reg = avaliable_reg;
                            var_ref_regs[arg->getNameCString()] = avaliable_reg;
                        }
                        auto const &entry =
                            m_symbol_manager.lookup(arg->getNameCString());

                        fprintf(stderr, "%d VariableReferenceNode %s reg: %s\n",
                                ind, entry->getNameCString(),
                                local_used_reg[ind].getNameCString());

                        if (entry->getLevel() == 0) {
                            snprintf(inst_buf_c_str, 1023,
                                     riscv_assembly_load_global,
                                     p_expr_reg.getNameCString(),
                                     entry->getNameCString(),
                                     entry->getNameCString(),
                                     p_expr_reg.getNameCString(), 0,
                                     p_expr_reg.getNameCString());
                        } else {
                            snprintf(inst_buf_c_str, 1023,
                                     riscv_assembly_load_local,
                                     p_expr_reg.getNameCString(),
                                     entry->getSp(), entry->getNameCString());
                        }
                    },
                    [&](FunctionInvocationNode *arg) {
                        if (p_expr_reg == 0)
                            p_expr_reg = GetAvailableReg();

                        auto const &parameters = arg->getArguments();
                        size_t arg_index = 0;
                        std::string func_invocation_inst_buf,
                            func_invocation_inst_buf_pre,
                            func_invocation_inst_buf_post;

                        // handle caller saved register
                        size_t reused_count = 0;
                        bool reuse_argument_reg = false;
                        std::set<RiscvRegister> saved_reg;

                        for (auto const &argu_reg : used_reg) {
                            char temp[1024];
                            snprintf(temp, 1023, "\t# used reg: %s\n",
                                     argu_reg.getNameCString());
                            func_invocation_inst_buf_pre += std::move(temp);

                            if (argu_reg.saved_caller() &&
                                argu_reg != p_expr_reg &&
                                (!saved_reg.count(argu_reg))) {
                                saved_reg.emplace(argu_reg);
                                reuse_argument_reg = true;
                                snprintf(
                                    inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
                                    "\tsw %s, %ld(sp)\t\t\t# save caller "
                                    "preserved "
                                    "register %s\t\t\t\n",
                                    argu_reg.getNameCString(), 4 * reused_count,
                                    argu_reg.getNameCString());
                                func_invocation_inst_buf_pre +=
                                    std::move(inst_buf_c_str);

                                snprintf(
                                    inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
                                    "\tlw %s, %ld(sp)\t\t\t# load caller "
                                    "preserved "
                                    "argument register %s\t\t\t\n",
                                    argu_reg.getNameCString(), 4 * reused_count,
                                    argu_reg.getNameCString());
                                func_invocation_inst_buf_post +=
                                    std::move(inst_buf_c_str);
                                reused_count++;
                            }
                        }

                        if (reuse_argument_reg) {
                            current_sp += reused_count * 4;
                            snprintf(inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
                                     "\taddi sp, sp, -%ld\n", reused_count * 4);
                            func_invocation_inst_buf_pre =
                                std::move(inst_buf_c_str) +
                                std::move(func_invocation_inst_buf_pre);

                            m_Inst_buff +=
                                std::move(func_invocation_inst_buf_pre);

                            snprintf(inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
                                     "\taddi sp, sp, %ld\n", reused_count * 4);
                            func_invocation_inst_buf_post +=
                                std::move(inst_buf_c_str);
                        }

                        // saved parameters to register
                        if (parameters.size() >= 8) {
                            snprintf(inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
                                     "\taddi sp, sp, -%ld\t\t\t# increase "
                                     "parameters stack\n",
                                     (parameters.size() - 8) << 2);
                            m_Inst_buff += std::move(inst_buf_c_str);
                            snprintf(inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
                                     "\taddi sp, sp, %ld\t\t\t# decrease "
                                     "parameters stack\n",
                                     (parameters.size() - 8) << 2);
                            func_invocation_inst_buf_post +=
                                std::move(inst_buf_c_str);
                        }
                        std::for_each(
                            parameters.begin(), parameters.end(),
                            [&](std::unique_ptr<ExpressionNode> const &arg) {
                                fprintf(stderr, "handle %ld argument\n",
                                        arg_index);
                                ThreeAddressCodeTable.clear();

                                const_cast<std::unique_ptr<ExpressionNode> &>(
                                    arg)
                                    ->accept(*this);

                                auto parameters_expr_res = ({
                                    std::vector<RiscvRegister> temp;
                                    if (arg_index < 8) {
                                        temp = expr_handler(
                                            0, ArgumentRegisters[arg_index]);
                                    } else {
                                        temp = expr_handler(
                                            0, RiscvRegisterEnum::zero);
                                    }
                                    std::move(temp);
                                });

                                RiscvRegister res_arg = parameters_expr_res[0];

                                if (arg_index < 8) {
                                    // Note: saved to argument register in
                                    // previous stage
                                    inst_buf_c_str[0] = '\0';
                                } else {
                                    snprintf(inst_buf_c_str,
                                             sizeof(inst_buf_c_str) - 1,
                                             "\tsw %s, %ld(sp)\t\t\t# save "
                                             "%ld parameters\n",
                                             res_arg.getNameCString(),
                                             (arg_index - 8) * 4, arg_index);
                                    m_Inst_buff += std::move(inst_buf_c_str);
                                    inst_buf_c_str[0] = '\0';
                                }

                                while (!m_Inst_stack.empty()) {
                                    func_invocation_inst_buf +=
                                        std::move(m_Inst_stack.top());
                                    m_Inst_stack.pop();
                                }

                                for (auto const &i : parameters_expr_res) {
                                    if (i == p_expr_reg ||
                                        (arg_index <
                                             sizeof(ArgumentRegisters) &&
                                         i == ArgumentRegisters[arg_index]))
                                        continue;
                                    ReturnReg(i);
                                }

                                func_invocation_inst_buf +=
                                    std::move(inst_buf_c_str);

                                arg_index++;
                            });

                        current_sp -= reused_count * 4;
                        fprintf(stderr,
                                "%d FunctionInvocationNode %s reg: %s\n", ind,
                                arg->getNameCString(),
                                p_expr_reg.getNameCString());

                        pre_inst_buf +=
                            // std::move(func_invocation_inst_buf_pre) +
                            std::move(func_invocation_inst_buf);
                        post_inst_buf +=
                            std::move(func_invocation_inst_buf_post);

                        if (p_expr_reg != RiscvRegisterEnum::a0)
                            snprintf(inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
                                     "\tcall %s\t\t\t\t# call function\n"
                                     "\tmv %s, a0\t\t\t\t# move return value "
                                     "to dest register\n",
                                     arg->getNameCString(),
                                     p_expr_reg.getNameCString());
                        else
                            snprintf(inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
                                     "\tcall %s\t\t\t\t# call function\n"
                                     "\t\t\t\t\t\t\t# dest register is %s\n",
                                     arg->getNameCString(),
                                     p_expr_reg.getNameCString());
                    },
                    [&](ConstantValueNode *arg) {
                        if (p_expr_reg == 0)
                            p_expr_reg = GetAvailableReg();

                        fprintf(stderr, "%d ConstantValueNode %s reg: %s\n",
                                ind, arg->getConstantValueCString(),
                                local_used_reg[ind].getNameCString());

                        snprintf(
                            inst_buf_c_str, 1023,
                            riscv_assmbly_load_constant_integer,
                            p_expr_reg.getNameCString(),
                            arg->getConstantPtr()->getConstantValueCString());
                    },
                    [&](const ThreeAddressCodeOp &arg) {
                        if (p_expr_reg == 0) {
                            p_expr_reg = GetAvailableReg();
                        }

                        auto &reg_left = local_used_reg[arg.left],
                             &reg_right = local_used_reg[arg.right];
                        reg_left = local_used_reg[ind];

                        if (arg.right != 0)
                            reg_right = GetAvailableReg();

                        fprintf(stderr, "%d Op left: %ld right: %ld reg: %s\n",
                                ind, arg.left, arg.right,
                                local_used_reg[ind].getNameCString());
                        switch (arg.op) {
                        case Operator::kNegOp:
                            snprintf(inst_buf_c_str, 1023,
                                     "\tneg %s, %s\t\t\t# neg op\n",
                                     reg_left.getNameCString(),
                                     reg_left.getNameCString());
                            break;
                        case Operator::kNotOp:
                            snprintf(inst_buf_c_str, 1023,
                                     "\txori %s, %s, 1\t\t\t# Not op\n"
                                     "\taddi %s, %s, 0xff\t\t\t# Not op\n",
                                     reg_left.getNameCString(),
                                     reg_left.getNameCString(),
                                     reg_left.getNameCString(),
                                     reg_left.getNameCString());
                            break;
                        case Operator::kLessOp:
                            snprintf(inst_buf_c_str, 1023,
                                     "\tslt %s, %s, %s\t\t\t# less op\n",
                                     reg_left.getNameCString(),
                                     reg_left.getNameCString(),
                                     reg_right.getNameCString());
                            break;
                        case Operator::kLessOrEqualOp:
                            snprintf(
                                inst_buf_c_str, 1023,
                                "\tsgt %s, %s, %s\t\t\t# less or equal op\n"
                                "\txori %s, %s, 1\n",
                                reg_left.getNameCString(),
                                reg_left.getNameCString(),
                                reg_right.getNameCString(),
                                reg_left.getNameCString(),
                                reg_left.getNameCString());
                            break;
                        case Operator::kGreaterOp:
                            snprintf(inst_buf_c_str, 1023,
                                     "\tsgt %s, %s, %s\t\t\t# greater op\n",
                                     reg_left.getNameCString(),
                                     reg_left.getNameCString(),
                                     reg_right.getNameCString());
                            break;
                        case Operator::kGreaterOrEqualOp:
                            snprintf(
                                inst_buf_c_str, 1023,
                                "\tslt %s, %s, %s\t\t\t# greater or equal op\n"
                                "\txori %s, %s, 1\n",
                                reg_left.getNameCString(),
                                reg_left.getNameCString(),
                                reg_right.getNameCString(),
                                reg_left.getNameCString(),
                                reg_left.getNameCString());
                            break;
                        case Operator::kEqualOp:
                            snprintf(inst_buf_c_str, 1023,
                                     "\tsub %s, %s, %s\t\t\t# eq operator\n"
                                     "\tseqz %s, %s\n",
                                     reg_left.getNameCString(),
                                     reg_left.getNameCString(),
                                     reg_right.getNameCString(),
                                     reg_left.getNameCString(),
                                     reg_left.getNameCString());
                            break;
                        case Operator::kNotEqualOp:
                            snprintf(inst_buf_c_str, 1023,
                                     "\tsub %s, %s, %s\t\t\t# neq operator\n"
                                     "\tsnez %s, %s\n",
                                     reg_left.getNameCString(),
                                     reg_left.getNameCString(),
                                     reg_right.getNameCString(),
                                     reg_left.getNameCString(),
                                     reg_left.getNameCString());
                            break;
                        default:
                            snprintf(inst_buf_c_str, 1023, riscv_assembly_op,
                                     kOpInstr[(uint8_t)arg.op],
                                     reg_left.getNameCString(),
                                     reg_left.getNameCString(),
                                     reg_right.getNameCString());
                        }
                    },
                    [&](const auto &arg) { fprintf(stderr, "Unknown\n"); }},
                e);
            ind++;
            if (dump_inst) {
                std::string inst_buf;
                inst_buf += std::move(pre_inst_buf) +
                            std::move(inst_buf_c_str) +
                            std::move(post_inst_buf);
                inst_stack.emplace(std::move(inst_buf));
            }
        });
    puts("");

    while (!inst_stack.empty()) {
        m_Inst_buff += inst_stack.top();
        inst_stack.pop();
    }

    return local_used_reg;
}

void CodeGenerator::visit(ProgramNode &p_program) {
    // Generate RISC-V instructions for program header
    // clang-format off
    constexpr const char *const riscv_assembly_file_prologue =
        "    .file \"%s\"\n"
        "    .option nopic\n"
        ".section    .text\n"
        "    .align 2\n";
    // clang-format on
    dumpInstructions(m_output_file.get(), riscv_assembly_file_prologue,
                     m_source_file_path.c_str());

    // Reconstruct the scope for looking up the symbol entry.
    // Hint: Use m_symbol_manager->lookup(symbol_name) to get the symbol entry.
    m_symbol_manager.pushScope(
        std::move(m_symbol_table_of_scoping_nodes.at(&p_program)));
    m_context_stack.push(CodeGenContext::kGlobal);

    auto visit_ast_node = [&](auto &ast_node) { ast_node->accept(*this); };
    for_each(p_program.getDeclNodes().begin(), p_program.getDeclNodes().end(),
             visit_ast_node);

    for_each(p_program.getFuncNodes().begin(), p_program.getFuncNodes().end(),
             visit_ast_node);

    constexpr const char *const riscv_assembly_main_func_begin =
        ".section\t.text\n"
        "\t.align 2\n"
        "\t.globl main\t\t\t# emit symbol 'main' to the global symbol "
        "table\n"
        "\t.type main, @function\n"
        ".LS0:\n"
        "\t.string \"%%d\\n\"\n"
        "\t.align 2\n"
        ".LS1:\n"
        "\t.string \"%%f\\n\"\n"
        "\t.align 2\n"
        "main:\n"
        "\taddi sp, sp, -8\n"
        "\tsw ra, 4(sp)\n"
        "\tsw s0, 0(sp)\n"
        "\tmv s0, sp\n"
        "\t# main start\n";

    dumpInstructions(m_output_file.get(), riscv_assembly_main_func_begin);

    m_context_stack.push(CodeGenContext::kLocal);
    const_cast<CompoundStatementNode &>(p_program.getBody()).accept(*this);
    m_context_stack.pop();

    constexpr const char *const riscv_assembly_main_func_end =
        "\t# main end\n"
        "\tmv a0, zero\n"
        "\tlw ra, 4(sp)\n"
        "\tlw s0, 0(sp)\n"
        "\taddi sp, sp, 8\n"
        "\tjr ra\n"
        "\t.size main, .-main\n";

    dumpInstructions(m_output_file.get(), riscv_assembly_main_func_end);

    while (!m_Inst_glob_stack.empty()) {
        dumpInstructions(m_output_file.get(), m_Inst_glob_stack.top().c_str());
        m_Inst_glob_stack.pop();
    }

    m_symbol_manager.popScope();
    m_context_stack.pop();
}

void CodeGenerator::visit(DeclNode &p_decl) {
    p_decl.visitChildNodes(*this);
}

void CodeGenerator::visit(VariableNode &p_variable) {

    auto const p_name = p_variable.getName().c_str();
    constexpr const char *const riscv_assembly_global_variable =
        "\t.comm %s, 4, 4\n";
    constexpr const char *const riscv_assembly_global_constant =
        ".section    .rodata\n"
        "\t.align 2\n"
        "\t.globl %s\n"
        "\t.type %s, @object\n"
        "%s:\n"
        "\t.word %s\n";

    constexpr const char *const riscv_assembly_local_integer_constant =
        "\tli %s, %s\n"
        "\tsw %s, %ld(s0)\n";
    constexpr const char *const riscv_assembly_local_float_constant =
        "\tla t0, .LC%ld\n"
        "\tflw ft1, %ld(t0)\n"
        "\tfsw ft1, %ld(s0)\n";
    constexpr const char *const riscv_assembly_local_float_constant_declare =
        ".LC%ld:\n"
        "\t.float %s\n";

    uint64_t dim = std::reduce(
        std::execution::par, p_variable.getTypePtr()->getDimensions().begin(),
        p_variable.getTypePtr()->getDimensions().end(), 1, std::multiplies<>());

    auto const &p_constant = p_variable.getConstantPtr();

    auto entry = m_symbol_manager.lookup(p_name);
    switch (m_context_stack.top()) {
    case CodeGenContext::kGlobal:
        if (!p_constant) {
            dumpInstructions(m_output_file.get(),
                             riscv_assembly_global_variable, p_name);
        } else {
            dumpInstructions(m_output_file.get(),
                             riscv_assembly_global_constant, p_name, p_name,
                             p_name, p_constant->getConstantValueCString());
        }
        break;
    case CodeGenContext::kFunction:
    default:
        size_t stack_depth = dim;

        switch (p_variable.getTypePtr()->getPrimitiveType()) {
        case PType::PrimitiveTypeEnum::kIntegerType: {
            stack_depth = INT_SIZE * dim;
            const_cast<SymbolEntry *>(entry)->setSp(current_sp);
            if (entry)
                fprintf(stderr, "var %s at %ld\n", p_name, entry->getSp());
        } break;
        case PType::PrimitiveTypeEnum::kRealType:
            stack_depth = FLOAT_SIZE * dim;
            const_cast<SymbolEntry *>(entry)->setSp(current_sp);
        default:
            break;
        }

        char inst_buf[1024] = {0};
        if (p_constant) {
            auto reg = RiscvRegister(RiscvRegisterEnum::t0);

            switch (p_variable.getTypePtr()->getPrimitiveType()) {
            case PType::PrimitiveTypeEnum::kIntegerType:
                snprintf(inst_buf, sizeof(inst_buf) - 1,
                         riscv_assembly_local_integer_constant,
                         reg.getNameCString(),
                         p_constant->getConstantValueCString(),
                         reg.getNameCString(), -current_sp - 4);
                m_Inst_stack.emplace(inst_buf);
                break;

            case PType::PrimitiveTypeEnum::kRealType:
                snprintf(inst_buf, sizeof(inst_buf) - 1,
                         riscv_assembly_local_float_constant,
                         LocalConstantLabel, 0LU, -current_sp - 4);
                m_Inst_stack.emplace(inst_buf);
                snprintf(inst_buf, sizeof(inst_buf) - 1,
                         riscv_assembly_local_float_constant_declare,
                         LocalConstantLabel,
                         p_constant->getConstantValueCString());
                m_Inst_glob_stack.emplace(inst_buf);

                LocalConstantLabel++;
                break;
            default:
                break;
            }
        }

        if (m_context_stack.top() != CodeGenContext::kFunction) {
            current_sp += stack_depth;
            break;
        }

        // for a0 ~ a7
        if (function_arg_index <= 7) {
            snprintf(inst_buf, sizeof(inst_buf) - 1,
                     "\tsw a%ld, %ld(s0)\t\t\t# save %s argument to memory\n",
                     function_arg_index, -current_sp - 4,
                     p_variable.getNameCString());
            m_Inst_stack.emplace(inst_buf);
            current_sp += stack_depth;
        } else {
            // ra + function argument
            const_cast<SymbolEntry *>(entry)->setSp(
                -((function_arg_index - 8) << 2) - 12);
        }

        function_arg_index++;
        break;
    }
}

void CodeGenerator::visit(ConstantValueNode &p_constant_value) {
    three_addr_ind = ThreeAddressCodeTable.size();
    ThreeAddressCodeTable.emplace_back(&p_constant_value);
}

void CodeGenerator::visit(FunctionNode &p_function) {
    // Reconstruct the scope for looking up the symbol entry.
    constexpr const char *const riscv_assembly_function_start_label =
        ".section\t.text\n"
        "\t.align 2\n"
        "\t.globl %s\n"
        "\t.type %s, @function\n"
        "%s:\n"
        "\taddi sp, sp, -8\n"
        "\tsw s0, 4(sp)\n"
        "\tsw ra, 0(sp)\n"
        "\tmv s0, sp\n";
    constexpr const char *const riscv_assembly_function_end =
        "\tlw ra, 0(sp)\n"
        "\tlw s0, 4(sp)\n"
        "\taddi sp, sp, 8\n"
        "\tjr ra\n"
        "\t.size %s, .-%s\n";

    auto prev_sp = current_sp;
    current_sp = 0;

    m_context_stack.emplace(CodeGenContext::kFunction);
    m_symbol_manager.pushScope(
        std::move(m_symbol_table_of_scoping_nodes.at(&p_function)));

    dumpInstructions(m_output_file.get(), riscv_assembly_function_start_label,
                     p_function.getNameCString(), p_function.getNameCString(),
                     p_function.getNameCString());

    std::string argument_inst_buf;
    auto &parameters = p_function.getParameters();
    function_arg_index = 0;
    for (auto &ast_node : parameters) {
        ast_node->accept(*this);
    };

    while (!m_Inst_stack.empty()) {
        // snprintf(temp_buf, sizeof(temp_buf) - 1, m_Inst_stack.top().c_str());
        argument_inst_buf += m_Inst_stack.top();
        m_Inst_stack.pop();
    }

    m_context_stack.emplace(CodeGenContext::kLocal);
    p_function.visitBodyChildNodes(*this);
    m_context_stack.pop();

    dumpInstructions(m_output_file.get(), riscv_assembly_add_stack_pointer,
                     (const size_t)current_sp);
    dumpInstructions(m_output_file.get(), argument_inst_buf.c_str());
    dumpInstructions(m_output_file.get(), m_Inst_buff.c_str());
    m_Inst_buff.clear();

    // Remove the entries in the hash table
    m_symbol_manager.popScope();
    m_context_stack.pop();

    dumpInstructions(m_output_file.get(), riscv_assembly_reset_stack_pointer,
                     current_sp);
    dumpInstructions(m_output_file.get(), riscv_assembly_function_end,
                     p_function.getNameCString(), p_function.getNameCString());
    current_sp = prev_sp;
}

void CodeGenerator::visit(CompoundStatementNode &p_compound_statement) {
    // Reconstruct the scope for looking up the symbol entry.
    auto visit_ast_node = [&](auto &ast_node) { ast_node->accept(*this); };
    auto prev_sp = current_sp;
    bool is_for_loop = m_context_stack.top() == CodeGenContext::kForLoop;
    char inst_buf[1024];
    std::string local_inst_buf;

    m_context_stack.emplace(CodeGenContext::kLocal);
    m_symbol_manager.pushScope(
        std::move(m_symbol_table_of_scoping_nodes.at(&p_compound_statement)));

    std::for_each(p_compound_statement.getDeclNodes().begin(),
                  p_compound_statement.getDeclNodes().end(), visit_ast_node);

    if (prev_sp != current_sp && !is_for_loop)
        dumpInstructions(m_output_file.get(), riscv_assembly_add_stack_pointer,
                         (const size_t)current_sp - prev_sp);
    else if (prev_sp != current_sp && is_for_loop) {
        snprintf(inst_buf, sizeof(inst_buf) - 1,
                 riscv_assembly_add_stack_pointer,
                 (const size_t)current_sp - prev_sp);
        local_inst_buf += std::move(inst_buf);
    }

    while (!m_Inst_stack.empty()) {
        if (!is_for_loop)
            dumpInstructions(m_output_file.get(), m_Inst_stack.top().c_str());
        else {
            local_inst_buf += m_Inst_stack.top();
        }
        m_Inst_stack.pop();
    }

    std::for_each(p_compound_statement.getStmtNodes().begin(),
                  p_compound_statement.getStmtNodes().end(), visit_ast_node);

    if (!is_for_loop) {
        dumpInstructions(m_output_file.get(), m_Inst_buff.c_str());
        m_Inst_buff.clear();
    } else {
        m_Inst_buff = std::move(local_inst_buf) + std::move(m_Inst_buff);
    }

    m_context_stack.pop();
    m_symbol_manager.popScope();

    if (prev_sp != current_sp && !is_for_loop) {
        dumpInstructions(m_output_file.get(),
                         riscv_assembly_reset_stack_pointer, current_sp);
    } else if (prev_sp != current_sp) {
        snprintf(inst_buf, sizeof(inst_buf) - 1,
                 riscv_assembly_reset_stack_pointer, current_sp);
        m_Inst_buff += std::move(inst_buf);
    }
    current_sp = prev_sp;
}

void CodeGenerator::visit(PrintNode &p_print) {
    bool a1_used = used_reg.count(RiscvRegisterEnum::a1);
    bool a0_used = used_reg.count(RiscvRegisterEnum::a0);
    constexpr const char *const riscv_assembly_print_reg =
        "\tadd a1, %s, zero\n"
        "\tla a0, %s\t\t\t\t#load str\n"
        "\tcall printf\n";

    used_reg.clear();
    ThreeAddressCodeTable.clear();

    p_print.visitChildNodes(*this);
    fprintf(stderr, "ThreeAddressCodeTable size: %ld\n",
            ThreeAddressCodeTable.size());

    auto local_used_reg = expr_handler(0, RiscvRegisterEnum::zero);
    assert(local_used_reg.size() >= 1);

    auto &reg = local_used_reg[0];
    char inst_buf[1024];

    if (a1_used) {
        snprintf(inst_buf, sizeof(inst_buf) - 1, riscv_assembly_sw, "a1", 0,
                 "sp");
        m_Inst_buff += inst_buf;
    }
    if (a0_used) {
        snprintf(inst_buf, sizeof(inst_buf) - 1, riscv_assembly_sw, "a0", 0,
                 "sp");
        m_Inst_buff += inst_buf;
    }

    snprintf(inst_buf, sizeof(inst_buf) - 1, riscv_assembly_print_reg,
             reg.getNameCString(), ".LS0");
    m_Inst_buff += inst_buf;

    if (a0_used) {
        snprintf(inst_buf, sizeof(inst_buf) - 1, riscv_assembly_lw, "a0", 0,
                 "sp");
        m_Inst_buff += inst_buf;
    }
    if (a1_used) {
        snprintf(inst_buf, sizeof(inst_buf) - 1, riscv_assembly_lw, "a1", 0,
                 "sp");
        m_Inst_buff += inst_buf;
    }

    std::for_each(local_used_reg.begin(), local_used_reg.end(),
                  [&](auto &used_reg) { ReturnReg(used_reg); });

    fprintf(stderr, "avaliable reg: %ld\nUsed: ", avaliable_reg.size());

    std::for_each(used_reg.begin(), used_reg.end(), [&](auto &reg) {
        fprintf(stderr, "%s ", reg.getNameCString());
    });
    puts("\n");
}

void CodeGenerator::visit(BinaryOperatorNode &p_bin_op) {
    size_t curr_ind = ThreeAddressCodeTable.size();
    ThreeAddressCodeTable.emplace_back(
        (ThreeAddressCodeOp){.op = p_bin_op.getOp(), .left = 0, .right = 0});

    auto const &left = p_bin_op.getLeftOperand();
    auto const &right = p_bin_op.getRightOperand();

    const_cast<ExpressionNode &>(left).accept(*this);
    std::get<ThreeAddressCodeOp>(ThreeAddressCodeTable[curr_ind]).left =
        three_addr_ind;

    const_cast<ExpressionNode &>(right).accept(*this);
    std::get<ThreeAddressCodeOp>(ThreeAddressCodeTable[curr_ind]).right =
        three_addr_ind;

    three_addr_ind = curr_ind;
}

void CodeGenerator::visit(UnaryOperatorNode &p_un_op) {
    size_t curr_ind = ThreeAddressCodeTable.size();
    ThreeAddressCodeTable.emplace_back((ThreeAddressCodeOp){
        .op = p_un_op.getOp(), .left = three_addr_ind, .right = 0});
    const_cast<ExpressionNode &>(p_un_op.getOperand()).accept(*this);

    std::get<ThreeAddressCodeOp>(ThreeAddressCodeTable[curr_ind]).left =
        three_addr_ind;
    three_addr_ind = curr_ind;
}

void CodeGenerator::visit(FunctionInvocationNode &p_func_invocation) {
    three_addr_ind = ThreeAddressCodeTable.size();
    ThreeAddressCodeTable.emplace_back(&p_func_invocation);
}

void CodeGenerator::visit(VariableReferenceNode &p_variable_ref) {
    three_addr_ind = ThreeAddressCodeTable.size();
    ThreeAddressCodeTable.emplace_back(std::addressof(p_variable_ref));
}

void CodeGenerator::visit(AssignmentNode &p_assignment) {
    constexpr const char *const riscv_assembly_assign_local =
        "\tsw %s, %d(s0)\t\t\t# assign local variable %s\n";
    constexpr const char *const riscv_assembly_assign_glob =
        "\tla %s, %s\t\t\t\t# load glob var from addr\n"
        "\tsw %s, %d(%s)\t\t\t# save value to glob\n";

    used_reg.clear();
    ThreeAddressCodeTable.clear();

    p_assignment.visitChildNodes(*this);

    auto const &assign_node = p_assignment.getLvalue();
    auto const &assign_entry = m_symbol_manager.lookup(assign_node.getName());

    auto local_used_reg = expr_handler(1, RiscvRegisterEnum::zero);
    assert(local_used_reg.size() >= 2);
    auto &result_reg = local_used_reg[1];
    char inst_buf[1024];

    if (assign_entry->getLevel() == 0) {
        auto glob_addr = GetAvailableReg();
        snprintf(inst_buf, sizeof(inst_buf) - 1, riscv_assembly_assign_glob,
                 glob_addr.getNameCString(), assign_entry->getNameCString(),
                 result_reg.getNameCString(), 0, glob_addr.getNameCString());
        ReturnReg(glob_addr);
    } else {
        snprintf(inst_buf, sizeof(inst_buf) - 1, riscv_assembly_assign_local,
                 result_reg.getNameCString(), (int)assign_entry->getSp(),
                 assign_node.getNameCString());
    }
    m_Inst_buff += std::move(inst_buf);

    std::for_each(local_used_reg.begin() + 1, local_used_reg.end(),
                  [&](auto &reg) { ReturnReg(reg); });
}

void CodeGenerator::visit(ReadNode &p_read) {
    bool a1_used = used_reg.count(RiscvRegisterEnum::a1);
    bool a0_used = used_reg.count(RiscvRegisterEnum::a0);
    constexpr const char *const riscv_assembly_read_variable =
        "\tla a0, %s\t\t\t\t#load str\n"
        "\tcall scanf\n";

    used_reg.clear();
    ThreeAddressCodeTable.clear();

    auto const &entry = m_symbol_manager.lookup(p_read.getTarget().getName());

    char inst_buf[1024];
    if (a1_used) {
        snprintf(inst_buf, sizeof(inst_buf) - 1, riscv_assembly_sw, "a1", 0,
                 "sp");
        m_Inst_buff += inst_buf;
    }
    if (a0_used) {
        snprintf(inst_buf, sizeof(inst_buf) - 1, riscv_assembly_sw, "a0", 0,
                 "sp");
        m_Inst_buff += inst_buf;
    }

    if (entry->getLevel() == 0) {
        snprintf(inst_buf, sizeof(inst_buf) - 1,
                 "\tla a1, %s\t\t\t# load address of global variable %s\n",
                 entry->getNameCString(), entry->getNameCString());
    } else {
        snprintf(inst_buf, sizeof(inst_buf) - 1,
                 "\taddi a1, sp, %ld\t\t\t# load address of variable %s\n",
                 entry->getSp(), entry->getNameCString());
    }
    m_Inst_buff += inst_buf;

    snprintf(inst_buf, sizeof(inst_buf) - 1, riscv_assembly_read_variable,
             ".LS0");
    m_Inst_buff += inst_buf;

    if (a0_used) {
        snprintf(inst_buf, sizeof(inst_buf) - 1, riscv_assembly_lw, "a0", 0,
                 "sp");
        m_Inst_buff += inst_buf;
    }
    if (a1_used) {
        snprintf(inst_buf, sizeof(inst_buf) - 1, riscv_assembly_lw, "a1", 0,
                 "sp");
        m_Inst_buff += inst_buf;
    }

    fprintf(stderr, "avaliable reg: %ld\nUsed: ", avaliable_reg.size());

    std::for_each(used_reg.begin(), used_reg.end(), [&](auto &reg) {
        fprintf(stderr, "%s ", reg.getNameCString());
    });
    puts("\n");
}

void CodeGenerator::visit(IfNode &p_if) {
    char inst_buf_c_str[1024];
    const auto &m_body = p_if.getBody();
    const auto &m_else_ptr = p_if.getElseBodyPtr();
    long if_body_label = BranchLabel, else_label, end_label = BranchLabel + 1;
    BranchLabel += 2;
    if (m_else_ptr) {
        else_label = BranchLabel;
        BranchLabel += 1;
    }

    const_cast<ExpressionNode &>(p_if.getCondition()).accept(*this);

    auto local_used_reg = expr_handler(0, RiscvRegisterEnum::zero);
    auto &result_reg = local_used_reg[0];

    snprintf(inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
             "\tbeq %s, zero, L%ld\t\t# if start\n"
             "L%ld:\n",
             result_reg.getNameCString(), m_else_ptr ? else_label : end_label,
             if_body_label);
    m_Inst_buff += inst_buf_c_str;

    std::for_each(local_used_reg.begin(), local_used_reg.end(),
                  [&](auto &reg) { ReturnReg(reg); });

    const_cast<CompoundStatementNode &>(m_body).accept(*this);
    if (m_else_ptr) {
        snprintf(inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
                 "\tj L%ld\n"
                 "L%ld:\t\t\t\t# else begin\n",
                 end_label, else_label);
        m_Inst_buff += inst_buf_c_str;
        const_cast<std::unique_ptr<CompoundStatementNode> &>(m_else_ptr)
            ->accept(*this);
    }

    snprintf(inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
             "L%ld:\t\t\t\t# if end\n", end_label);
    m_Inst_buff += inst_buf_c_str;
}

void CodeGenerator::visit(WhileNode &p_while) {
    long l1 = BranchLabel, l2 = BranchLabel + 1, l3 = BranchLabel + 2;
    BranchLabel += 3;
    char inst_buf_c_str[1024];

    snprintf(inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
             "L%lu:\t\t\t\t# while loop start\n", l1);
    m_Inst_buff += inst_buf_c_str;

    const_cast<ExpressionNode &>(p_while.getCondition()).accept(*this);
    auto local_used_reg = expr_handler(0, RiscvRegisterEnum::zero);
    auto &result_reg = local_used_reg[0];

    snprintf(inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
             "\tbeq %s, zero, L%lu\n"
             "L%lu:\t\t\t\t# while loop body\n",
             result_reg.getNameCString(), l3, l2);
    m_Inst_buff += inst_buf_c_str;
    std::for_each(local_used_reg.begin(), local_used_reg.end(),
                  [&](auto &reg) { ReturnReg(reg); });

    const_cast<CompoundStatementNode &>(p_while.getBody()).accept(*this);
    snprintf(inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
             "\tj L%ld\n"
             "L%ld:\t\t\t\t# while loop end\n",
             l1, l3);
    m_Inst_buff += inst_buf_c_str;
}

void CodeGenerator::visit(ForNode &p_for) {
    // Reconstruct the scope for looking up the symbol entry.
    m_symbol_manager.pushScope(
        std::move(m_symbol_table_of_scoping_nodes.at(&p_for)));
    long l1 = BranchLabel, l2 = BranchLabel + 1, l3 = BranchLabel + 2;

    BranchLabel += 3;
    size_t prev_sp = current_sp;
    char inst_buf_c_str[2048];
    std::string inst_buf, prev_inst_buf = std::move(m_Inst_buff);

    auto const &lower = p_for.getLowerBound();
    auto const &upper = p_for.getUpperBound();

    m_context_stack.emplace(CodeGenContext::kForLoop);
    const_cast<std::unique_ptr<DeclNode> &>(p_for.getDeclNode())->accept(*this);
    const_cast<std::unique_ptr<AssignmentNode> &>(p_for.getInit())
        ->accept(*this);
    const_cast<std::unique_ptr<ExpressionNode> &>(p_for.getEnd())
        ->accept(*this);

    // handle i init value
    auto reg_loop_var = GetAvailableReg();
    snprintf(inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
             "\taddi sp, sp, -%ld\t\t\t# for loop var\n", current_sp - prev_sp);
    inst_buf += std::move(inst_buf_c_str);
    inst_buf += std::move(m_Inst_buff);
    m_Inst_buff.clear();

    auto const &loop_var_name =
        p_for.getDeclNode()->getVariables()[0]->getNameCString();
    auto const &loop_var_entry = m_symbol_manager.lookup(loop_var_name);

    // handle end condition for loop
    auto reg_upper_bound = GetAvailableReg();
    snprintf(inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
             "L%ld:\n"
             "\tlw %s, %ld(s0)\t\t\t# load loop var\n"
             "\tli %s, %s\t\t\t# load upper bound\n"
             "\tbge %s, %s, L%ld\n",
             l1, reg_loop_var.getNameCString(), loop_var_entry->getSp(),
             reg_upper_bound.getNameCString(), upper.getConstantValueCString(),
             reg_loop_var.getNameCString(), reg_upper_bound.getNameCString(),
             l3);
    inst_buf += std::move(inst_buf_c_str);
    ReturnReg(reg_upper_bound);
    ReturnReg(reg_loop_var);

    snprintf(inst_buf_c_str, sizeof(inst_buf_c_str) - 1, "L%ld:\n", l2);
    inst_buf += std::move(inst_buf_c_str);

    // loop body
    const_cast<std::unique_ptr<CompoundStatementNode> &>(p_for.getBody())
        ->accept(*this);
    inst_buf += m_Inst_buff;

    // i+= 1
    reg_loop_var = GetAvailableReg();
    snprintf(inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
             "\tlw %s, %ld(s0)\t\t\t# load loop var\n"
             "\taddi %s, %s, 1\t\t\t# loop var += 1\n"
             "\tsw %s, %ld(s0)\t\t\t# save loop var\n"
             "\tj L%ld\n",
             reg_loop_var.getNameCString(), loop_var_entry->getSp(),
             reg_loop_var.getNameCString(), reg_loop_var.getNameCString(),
             reg_loop_var.getNameCString(), loop_var_entry->getSp(), l1);
    inst_buf += std::move(inst_buf_c_str);
    ReturnReg(reg_loop_var);

    snprintf(inst_buf_c_str, sizeof(inst_buf_c_str) - 1,
             "L%ld:\n"
             "\taddi sp, sp, %ld\t\t\t# end for loop\n",
             l3, current_sp - prev_sp);
    inst_buf += std::move(inst_buf_c_str);

    // Remove the entries in the hash table
    m_context_stack.pop();
    m_symbol_manager.popScope();
    current_sp = prev_sp;
    m_Inst_buff = std::move(prev_inst_buf) + inst_buf;
}

void CodeGenerator::visit(ReturnNode &p_return) {
    p_return.visitChildNodes(*this);

    // return value
    auto local_used_reg = expr_handler(0, RiscvRegisterEnum::a0);
    char buf[1024];
    snprintf(buf, sizeof(buf) - 1,
             "\tlw ra, 0(s0)\n"
             "\taddi sp, s0, 8\n"
             "\tlw s0, 4(s0)\n"
             "\tjr ra\t\t\t\t# return\n");
    m_Inst_buff += std::move(buf);

    std::for_each(local_used_reg.begin(), local_used_reg.end(),
                  [&](auto &reg) { ReturnReg(reg); });
}
