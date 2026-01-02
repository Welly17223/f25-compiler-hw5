#include "codegen/CodeGenerator.hpp"
#include "AST/CompoundStatement.hpp"
#include "AST/ConstantValue.hpp"
#include "AST/FunctionInvocation.hpp"
#include "AST/VariableReference.hpp"
#include "AST/decl.hpp"
#include "AST/expression.hpp"
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
#include <cstring>
#include <functional>
#include <initializer_list>
#include <iostream>
#include <iterator>
#include <list>
#include <memory>
#include <pstl/glue_execution_defs.h>
#include <queue>
#include <sstream>
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
    if (m_context_stack.top() == CodeGenContext::kForLoopIfWhile) {
        return SymbolEntry::KindEnum::kLoopVarKind;
    }

    if (m_context_stack.top() == CodeGenContext::kFunction) {
        return SymbolEntry::KindEnum::kParameterKind;
    }

    // global or local
    return p_variable.getConstantPtr() ? SymbolEntry::KindEnum::kConstantKind
                                       : SymbolEntry::KindEnum::kVariableKind;
}

bool CodeGenerator::isShadowingLoopVar(const std::string &p_name) const {
    auto to_be_shadowed = m_symbol_manager.lookup(p_name);
    return to_be_shadowed &&
           to_be_shadowed->getKind() == SymbolEntry::KindEnum::kLoopVarKind;
}

bool CodeGenerator::isRedeclaringSymbol(const std::string &p_name) const {
    return m_symbol_manager.getCurrentTable()->lookup(p_name);
}

CodeGenerator::RiscvRegister CodeGenerator::GetAvailableReg() {
    if (avaliable_reg.size() == 0)
        return RiscvRegisterEnum::NO_REG;

    auto reg = *avaliable_reg.begin();
    avaliable_reg.erase(reg);
    fprintf(stderr, "used: %s\n", reg.getNameCString());
    return reg;
}

CodeGenerator::RiscvRegister CodeGenerator::GetAvailableReg(RiscvRegister reg) {
    if (avaliable_reg.count(reg) == 0)
        return RiscvRegisterEnum::NO_REG;

    avaliable_reg.erase(reg);
    used_reg.insert(reg);

    return reg;
}

void CodeGenerator::ReturnReg(RiscvRegister reg) {
    if (reg == RiscvRegisterEnum::zero)
        return;
    used_reg.erase(reg);
    avaliable_reg.insert(reg);
    fprintf(stderr, "return: %s\n", reg.getNameCString());
}

std::vector<CodeGenerator::RiscvRegister>
CodeGenerator::expr_handler(size_t start_ind, RiscvRegister ret_reg,
                            std::string &inst_buf) {
    std::string temp = std::move(m_Inst_buff);
    m_Inst_buff.clear();
    auto ret_val = expr_handler(start_ind, ret_reg);
    inst_buf += std::move(m_Inst_buff);
    m_Inst_buff = std::move(temp);
    return ret_val;
}

std::vector<CodeGenerator::RiscvRegister>
CodeGenerator::expr_handler(size_t start_ind, RiscvRegister ret_reg) {
    std::vector<RiscvRegister> local_used_reg(ThreeAddressCodeTable.size());

    std::vector<size_t> local_used_virtual_reg(ThreeAddressCodeTable.size());
    {
        size_t reverse_count = ThreeAddressCodeTable.size() * 2;
        /* std::for_each(ThreeAddressCodeTable.begin(),
                      ThreeAddressCodeTable.end(), [&](const auto &e) {
                          std::visit(
                              overloaded{
                                  [&](ThreeAddressFuncInvocation &arg) {
                                      reverse_count +=
                                          arg.func->getArguments().size();
                                  },
                                  [&](auto &arg) {},
                              },
                              e);
                      }); */
        local_used_virtual_reg.reserve(reverse_count);
    }

    auto localThreeAddressCodeTable = std::move(ThreeAddressCodeTable);

    if (ret_reg != RiscvRegisterEnum::zero) {
        local_used_reg[start_ind] = ret_reg;
        used_reg.emplace(ret_reg);
        avaliable_reg.erase(ret_reg);
    }

    std::unordered_map<std::string, RiscvRegister> var_ref_regs;
    std::unordered_map<std::string, size_t> var_ref_virtual_regs;
    std::map<size_t, size_t> virtual_regs_ref_mapping;
    size_t virtual_mem_counter = 1;
    auto get_virt_reg = [&]() -> size_t {
        virtual_mem_counter++;
        return virtual_mem_counter - 1;
    };
    std::list<Inst_virt_reg> virt_reg_inst_stack;
    std::stack<std::string> inst_stack;

    fprintf(stderr, "========== start expr_handler ==========\n");

    std::unordered_map<std::string, size_t> VariableRefLastUsed;
    size_t ind = start_ind;
    std::for_each(
        localThreeAddressCodeTable.begin(), localThreeAddressCodeTable.end(),
        [&](const auto &e) {
            std::visit(
                overloaded{[&](VariableReferenceNode *arg) {
                               VariableRefLastUsed[arg->getNameCString()] =
                                   ind - start_ind;
                           },
                           [&](auto &arg) {}},
                e);
            ind++;
        });

    for (auto &i : VariableRefLastUsed) {
        printf("%s: %ld\n", i.first.c_str(), i.second);
    }

    ind = start_ind;
    std::for_each(
        localThreeAddressCodeTable.begin() + start_ind,
        localThreeAddressCodeTable.end(), [&](const auto &e) {
            size_t &p_expr_virt_reg = local_used_virtual_reg[ind];
            bool dump_inst = true;
            char inst_buf_c_str[1024];

            std::vector<Inst_virt_reg> current_inst;

            std::visit(
                overloaded{
                    [&](VariableReferenceNode *arg) {
                        long origional_virt_reg = p_expr_virt_reg;
                        if (var_ref_virtual_regs.count(arg->getNameCString())) {
                            virtual_regs_ref_mapping[p_expr_virt_reg] =
                                var_ref_virtual_regs[arg->getNameCString()];

                            p_expr_virt_reg =
                                var_ref_virtual_regs[arg->getNameCString()];
                        } else if (p_expr_virt_reg == 0) {
                            p_expr_virt_reg = get_virt_reg();
                            var_ref_virtual_regs[arg->getNameCString()] =
                                p_expr_virt_reg;
                        } else {
                            var_ref_virtual_regs[arg->getNameCString()] =
                                p_expr_virt_reg;
                        }

                        if (ind != VariableRefLastUsed[arg->getName()]) {
                            dump_inst = false;
                        }

                        auto const &entry =
                            m_symbol_manager.lookup(arg->getNameCString());

                        fprintf(stderr,
                                "%lu VariableReferenceNode %s reg: tmp%ld, "
                                "origional: %ld\n",
                                ind, entry->getNameCString(), p_expr_virt_reg,
                                origional_virt_reg);

                        if (entry->getLevel() == 0) {
                            char temp[64];
                            local_used_virtual_reg.emplace_back(get_virt_reg());
                            snprintf(temp, 63, "la %%s, %s",
                                     entry->getNameCString());

                            size_t &temp_virt_reg =
                                local_used_virtual_reg.back();
                            current_inst.emplace_back(temp, temp_virt_reg);

                            snprintf(temp, 63, "lw %%s, 0(%%s)");
                            current_inst.emplace_back(
                                temp, p_expr_virt_reg,
                                std::initializer_list<size_t *>{
                                    &temp_virt_reg});
                        } else {
                            char temp[64];
                            snprintf(temp, 63, "lw %%s, %ld(s0)",
                                     entry->getSp());
                            current_inst.emplace_back(temp, p_expr_virt_reg);
                        }
                    },
                    [&](const ThreeAddressCodeFuncInvocation &arg) {
                        if (p_expr_virt_reg == 0)
                            p_expr_virt_reg = get_virt_reg();

                        std::string func_invocation_inst_buf_pre;

                        std::vector<Inst_virt_reg> parameters_inst;
                        std::vector<size_t *> parameters_tmp_register(
                            arg.func->getArguments().size());
                        size_t arg_length = arg.func->getArguments().size();

                        fprintf(stderr,
                                "%lu FunctionInvocationNode %s reg: tmp%ld "
                                "argument reg: ",
                                ind, arg.func->getNameCString(),
                                p_expr_virt_reg);

                        for (auto &i : arg.parameters) {
                            fprintf(stderr, "%lu ", i);
                        }
                        fputs("\n", stderr);

                        // FIXME: save argmuent register and other caller saved
                        // register

                        // add parameters and save it to temp register
                        for (auto &i : parameters_inst) {
                            current_inst.emplace_back(std::move(i));
                        }

                        // move register to argument register
                        char temp[64];
                        if (arg_length > 8) {
                            snprintf(temp, 63, "\taddi sp, sp, -%ld\n",
                                     (arg_length - 8) * 4);
                            current_inst.emplace_back(temp);
                        }
                        for (size_t i = 0; i < arg_length; i++) {
                            parameters_tmp_register[i] =
                                &local_used_virtual_reg[arg.parameters[i]];

                            std::optional<Inst_virt_reg> temp_inst;
                            if (i < 8) {
                                snprintf(temp, 63, "mv %s, %%s",
                                         ArgumentRegisters[i].getNameCString());
                                temp_inst.emplace(
                                    temp, 0,
                                    std::initializer_list<size_t *>{
                                        parameters_tmp_register[i]});
                                temp_inst.value().real_reg_write.emplace(
                                    ArgumentRegisters[i]);
                            } else {
                                snprintf(temp, 63, "sw %%s, %ld(sp)",
                                         (((long)i) - 8) * 4);
                                temp_inst.emplace(
                                    temp, 0,
                                    std::initializer_list<size_t *>{
                                        parameters_tmp_register[i]});
                            }
                            current_inst.emplace_back(
                                std::move(temp_inst.value()));
                        }

                        // function call
                        snprintf(temp, 63, "\tcall %s\n",
                                 arg.func->getNameCString());
                        current_inst.emplace_back(
                            temp, std::initializer_list<size_t *>{},
                            arg.func->getArguments().size());
                        auto &virt_reg_inst = current_inst.back();

                        if (arg_length > 0) {
                            auto &real_reg_list =
                                virt_reg_inst.real_reg_read.emplace();
                            size_t accu_arg_reg =
                                arg_length < 8 ? arg_length : 8;

                            for (size_t i = 0; i < accu_arg_reg; i++) {
                                real_reg_list.emplace_back(
                                    ArgumentRegisters[i]);
                            }

                            /* fputs("read: ", stderr);
                            for (auto &i :
                                 virt_reg_inst.real_reg_read.value()) {
                                fprintf(stderr, "%s", i.getNameCString());
                            }
                            fputs("\n", stderr); */
                        }

                        if (arg_length > 8) {
                            snprintf(temp, 63, "\taddi sp, sp, %ld\n",
                                     (arg_length - 8) * 4);
                            current_inst.emplace_back(temp);
                        }

                        // function return value
                        current_inst.emplace_back("mv %s, a0", p_expr_virt_reg);
                    },
                    [&](ConstantValueNode *arg) {
                        if (p_expr_virt_reg == 0)
                            p_expr_virt_reg = get_virt_reg();

                        char temp[64];
                        snprintf(
                            temp, 63, "li %%s, %s",
                            arg->getConstantPtr()->getConstantValueCString());

                        current_inst.emplace_back(temp, p_expr_virt_reg);
                    },
                    [&](const ThreeAddressCodeOp &arg) {
                        // alloc virt reg
                        if (p_expr_virt_reg == 0)
                            p_expr_virt_reg = get_virt_reg();

                        // local_used_virtual_reg[arg.left] = get_virt_reg();
                        size_t *virt_reg_left =
                                   &local_used_virtual_reg[arg.left],
                               *virt_reg_right =
                                   &local_used_virtual_reg[arg.right];

                        if (arg.right != 0) {
                            // virt_reg_right = get_virt_reg();
                        }

                        fprintf(stderr,
                                "%lu Op reg: tmp%ld, left[%ld]: %ld, "
                                "right[%ld]: %ld\n",
                                ind, p_expr_virt_reg, arg.left, *virt_reg_left,
                                arg.right, *virt_reg_right);
                        switch (arg.op) {
                        case Operator::kNegOp:
                            current_inst.emplace_back(
                                "neg %s, %s", p_expr_virt_reg,
                                std::initializer_list<size_t *>{virt_reg_left});
                            break;
                        case Operator::kNotOp:
                            current_inst.emplace_back(
                                "xori %s, %s, 1", p_expr_virt_reg,
                                std::initializer_list<size_t *>{virt_reg_left});
                            current_inst.emplace_back(
                                "addi %s, %s, 0xff", get_virt_reg(),
                                std::initializer_list<size_t *>{
                                    &p_expr_virt_reg});
                            break;
                        case Operator::kLessOp:
                            current_inst.emplace_back(
                                "slt %s, %s, %s", p_expr_virt_reg,
                                std::initializer_list<size_t *>{
                                    virt_reg_left, virt_reg_right});
                            break;
                        case Operator::kLessOrEqualOp:
                            current_inst.emplace_back(
                                "sgt %s, %s, %s", p_expr_virt_reg,
                                std::initializer_list<size_t *>{
                                    virt_reg_left, virt_reg_right});
                            current_inst.emplace_back(
                                "xori %s, %s, 1", get_virt_reg(),
                                std::initializer_list<size_t *>{
                                    &p_expr_virt_reg});
                            break;
                        case Operator::kGreaterOp:
                            current_inst.emplace_back(
                                "sgt %s, %s, %s", p_expr_virt_reg,
                                std::initializer_list<size_t *>{
                                    virt_reg_left, virt_reg_right});
                            break;
                        case Operator::kGreaterOrEqualOp:
                            current_inst.emplace_back(
                                "slt %s, %s, %s", p_expr_virt_reg,
                                std::initializer_list<size_t *>{
                                    virt_reg_left, virt_reg_right});
                            current_inst.emplace_back(
                                "xori %s, %s, 1", get_virt_reg(),
                                std::initializer_list<size_t *>{
                                    &p_expr_virt_reg});
                            break;
                        case Operator::kEqualOp:
                            current_inst.emplace_back(
                                "sub %s, %s, %s", p_expr_virt_reg,
                                std::initializer_list<size_t *>{
                                    virt_reg_left, virt_reg_right});
                            current_inst.emplace_back(
                                "seqz %s, %s", get_virt_reg(),
                                std::initializer_list<size_t *>{
                                    &p_expr_virt_reg});
                            break;
                        case Operator::kNotEqualOp:
                            current_inst.emplace_back(
                                "sub %s, %s, %s", p_expr_virt_reg,
                                std::initializer_list<size_t *>{
                                    virt_reg_left, virt_reg_right});
                            current_inst.emplace_back(
                                "snez %s, %s, 1", get_virt_reg(),
                                std::initializer_list<size_t *>{
                                    &p_expr_virt_reg});
                            break;
                        default:
                            char temp[64];
                            snprintf(temp, 63, "%s %%s, %%s, %%s",
                                     kOpInstr[(size_t)arg.op]);

                            current_inst.emplace_back(
                                temp, p_expr_virt_reg,
                                std::initializer_list<size_t *>{
                                    virt_reg_left, virt_reg_right});
                        }
                    },
                    [&](const auto &arg) { fprintf(stderr, "Unknown\n"); }},
                e);
            ind++;
            if (dump_inst) {
                std::string inst_buf;
                inst_buf += std::move(inst_buf_c_str);
                inst_stack.emplace(std::move(inst_buf));

                std::for_each(current_inst.rbegin(), current_inst.rend(),
                              [&](Inst_virt_reg &inst) {
                                  virt_reg_inst_stack.emplace_back(
                                      std::move(inst));
                              });
            }
        });

    // virtual register attribute
    size_t origional_sp = current_sp;
    std::vector<liveRange> virt_reg_live_range(virtual_mem_counter);
    std::vector<RiscvRegister> virt_real_reg_map(virtual_mem_counter);
    std::vector<size_t> virt_reg_memory(virtual_mem_counter);
    std::vector<bool> virt_reg_cross_function_call(virtual_mem_counter);
    std::vector<bool> virt_reg_is_spilled(virtual_mem_counter);
    std::vector<size_t> virt_reg_spilled_sp(virtual_mem_counter);
    std::vector<size_t> function_call_index;

    std::map<RiscvRegister, std::vector<liveRange>> real_reg_mat;

    // Give id to each instructions
    {
        size_t inst_ind = 0;
        std::for_each(
            virt_reg_inst_stack.begin(), virt_reg_inst_stack.end(),
            [&](Inst_virt_reg &inst) {
                inst.id = inst_ind;
                inst_ind += 2;
                if (inst.is_function_call && inst.function_inst == Inst::call) {
                    function_call_index.emplace_back(inst.id);
                }
                if (inst.is_function_call && inst.function_inst == Inst::lw) {
                    for (int i = 0; i < 8; i++) {
                        size_t offset = inst.n_argmument * 2;
                        real_reg_mat[ArgumentRegisters[i]].emplace_back(
                            liveRange{inst.id,
                                      inst.id > offset ? inst.id - offset : 0});
                    }
                }
            });
    }

    // compute virtual register live cycle
    // FIX: allocate s1~s9 to virtual register crossing the functino call
    for (int i = 0; i < 32; i++) {
        auto reg = RiscvRegister(i);
        std::vector<liveRange> v;
        if (reg.saved_callee() ^ reg.saved_caller()) {
            real_reg_mat[reg] = v;
        }
    }

    // for compute real register live cycle
    std::map<RiscvRegister, size_t> real_reg_start_time;

    for (auto it = virt_reg_inst_stack.begin(); it != virt_reg_inst_stack.end();
         it++) {
        if (it->true_inst)
            continue;

        if (it == virt_reg_inst_stack.begin())
            continue;

        for (auto j = std::prev(it); j != virt_reg_inst_stack.begin(); j--) {
            it->liveOut.insert(j->liveIn.begin(), j->liveIn.end());
        }

        // used
        if (it->read_regs)
            for (auto &j : *it->read_regs) {
                it->liveIn.insert(*j);
            }

        it->liveIn.insert(it->liveOut.begin(), it->liveOut.end());

        // erase var that defined in the block
        it->liveIn.erase(it->write_reg);

        // calculate argument live time
        if (it->real_reg_write.has_value()) {
            real_reg_mat[it->real_reg_write.value()].emplace_back(
                liveRange{.start = it->id, .end = it->id});

            real_reg_start_time.erase(it->real_reg_write.value());
            printf("%s start at %ld\n",
                   it->real_reg_write.value().getNameCString(), it->id);
        }

        if (it->real_reg_read.has_value()) {
            for (auto &j : it->real_reg_read.value()) {
                printf("%s end at %ld\n", j.getNameCString(), it->id);
                real_reg_start_time[j] = it->id;
            }
        }
    }

    for (auto it = virt_reg_inst_stack.rbegin();
         it != virt_reg_inst_stack.rend(); it++) {
        if (it->true_inst || it->is_function_call)
            continue;
        // Every temp reg only be written once
        if (it->write_reg != -1)
            virt_reg_live_range[it->write_reg].start = it->id;

        if (!it->liveOut.count(it->write_reg)) {
            virt_reg_live_range[it->write_reg].end = it->id;
        }

        if (it->read_regs) {
            const auto &read_regs = it->read_regs;
            for (const auto &j : *read_regs) {
                if (!it->liveOut.count(*j)) {
                    virt_reg_live_range[*j].end = it->id;
                }
            }
        }
    }

    // check if the tmp register cross function
    for (auto it = virt_reg_live_range.begin() + 1;
         it != virt_reg_live_range.end(); it++) {
        size_t index = std::distance(virt_reg_live_range.begin(), it);
        bool is_cross_function = false;

        for (auto &j : function_call_index) {
            if (it->start > j && j > it->end) {
                is_cross_function = true;

                break;
            }
        }
        virt_reg_cross_function_call[index] = is_cross_function;
    }

    // assign interval that used argument register

    // assign actual register
    for (auto current = virt_reg_live_range.begin() + 1;
         current != virt_reg_live_range.end(); current++) {
        size_t ind = std::distance(virt_reg_live_range.begin(), current);

        bool is_free = true;

        for (auto &i : real_reg_mat) {
            is_free = true;
            // printf("try %s:\n", i.first.getNameCString());

            // Assign tmp register that will cross function call to s1~s9
            if (virt_reg_cross_function_call[ind] == true &&
                !i.first.saved_callee()) {
                is_free = false;
                continue;
            }

            for (auto &j : i.second) {
                if (j.overlape(*current)) {
                    is_free = false;
                    break;
                }
            }

            if (is_free == true) {
                /* printf("done, tmp%ld choosing %s\n\n", ind,
                       i.first.getNameCString()); */
                virt_real_reg_map[ind] = i.first;
                function_used_reg.insert(i.first);
                i.second.emplace_back(*current);
                break;
            }
        }

        if (is_free) {
            virt_reg_is_spilled[ind] = false;
            continue;
        }

        // Spill
        virt_reg_is_spilled[ind] = true;
        virt_reg_spilled_sp[ind] = current_sp;
        current_sp += 4;
    }

    for (size_t i = 1LU; i < virt_real_reg_map.size(); i++) {
        fprintf(stderr, "tmp%lu: [%ld, %ld] %s\n", i,
                virt_reg_live_range[i].start, virt_reg_live_range[i].end,
                virt_real_reg_map[i].getNameCString());
    }
    for (auto &i : real_reg_mat) {
        fprintf(stderr, "%s: ", i.first.getNameCString());
        for (auto &j : i.second) {
            fprintf(stderr, "{%lu, %ld} ", j.start, j.end);
        }
        fputs("\n", stderr);
    }
    for (auto it = virt_reg_inst_stack.rbegin();
         it != virt_reg_inst_stack.rend(); it++) {
        auto &i = *it;
        if (i.true_inst || i.is_function_call)
            continue;
        int space_len = 20;
        printf("%-*s", space_len, i.inst.c_str());
        if (i.write_reg != -1)
            printf("write: %s(tmp%ld)\t",
                   virt_real_reg_map[i.write_reg].getNameCString(),
                   i.write_reg);
        if (i.read_regs) {
            printf("read: ");
            for (auto &j : *i.read_regs)
                printf("%s(tmp%ld) ", virt_real_reg_map[*j].getNameCString(),
                       *j);
        }
        puts("");
    }

    if (ret_reg != RiscvRegisterEnum::zero) {
        auto it = virt_reg_inst_stack.begin();
        while ((it->true_inst || it->is_function_call)) {
            it = std::next(it);
            assert(it != virt_reg_inst_stack.end());
        }
        virt_real_reg_map[it->write_reg] = ret_reg;
    }

    std::set<RiscvRegister> func_used_reg;
    for (auto it = virt_reg_inst_stack.rbegin();
         it != virt_reg_inst_stack.rend(); it++) {
        char temp_buf[2048] = {0};
        char temp_buf_end[4096] = {0};
        if (it->true_inst) {
            m_Inst_buff += it->inst;
        } else if (it->is_function_call) {
            size_t ind = std::distance(virt_reg_inst_stack.rbegin(), it);

            switch (it->function_inst) {
            case Inst::sw: {
                int local_ind_counter = 0;
                if (func_used_reg.size() > 0) {

                    for (auto &i : func_used_reg) {
                        snprintf(
                            temp_buf, sizeof(temp_buf) - 1,
                            "\tlw %s, %d(sp)\t\t\t# func call load register\n",
                            i.getNameCString(), local_ind_counter * 4);
                        local_ind_counter++;
                        m_Inst_buff += temp_buf;
                    }
                    snprintf(temp_buf, sizeof(temp_buf) - 1,
                             "\taddi sp, sp, %lu\t\t\t# func call %lu load\n",
                             func_used_reg.size() * 4, func_used_reg.size());
                    m_Inst_buff += temp_buf;
                }
            } break;
            case Inst::lw: {
                int local_ind_counter = 0;
                auto local_it = std::next(it);
                while (!(local_it->is_function_call &&
                         local_it->function_inst == Inst::sw) &&
                       local_it != virt_reg_inst_stack.rend()) {
                    local_it = std::next(local_it);
                }
                size_t sw_offset = std::distance(it, local_it) * 2;
                sprintf(temp_buf, "\t# %lu check overlape at %lu %lu\n", ind,
                        it->id, it->id - sw_offset);
                m_Inst_buff += temp_buf;

                for (long i = 1; i < (long)virt_real_reg_map.size(); i++) {
                    sprintf(temp_buf, "\t# cmp at tmp%ld [%ld, %ld]: %s\n", i,
                            virt_reg_live_range[i].start,
                            virt_reg_live_range[i].end,
                            virt_real_reg_map[i].getNameCString());
                    m_Inst_buff += temp_buf;
                    if (i != it->write_reg &&
                        virt_reg_live_range[i].start >= it->id &&
                        virt_reg_live_range[i].overlape(
                            liveRange{it->id, it->id - sw_offset})) {
                        func_used_reg.insert(
                            virt_real_reg_map[local_ind_counter]);
                    }
                    local_ind_counter++;
                }

                if (func_used_reg.size() > 0) {
                    snprintf(temp_buf, sizeof(temp_buf) - 1,
                             "\taddi sp, sp, -%lu\t\t\t# func call %lu saved\n",
                             func_used_reg.size() << 2,
                             func_used_reg.size() + 1);
                    m_Inst_buff += temp_buf;

                    local_ind_counter = 0;
                    for (auto &i : func_used_reg) {
                        snprintf(
                            temp_buf, sizeof(temp_buf) - 1,
                            "\tsw %s, %d(sp)\t\t\t# func call save register\n",
                            i.getNameCString(), local_ind_counter * 4);
                        local_ind_counter++;
                        m_Inst_buff += temp_buf;
                    }
                }
            } break;
            case Inst::call:
                m_Inst_buff += it->inst;
                break;
            }
        } else {
            size_t read_regs_length = 0;
            if (it->read_regs)
                read_regs_length = it->read_regs->size();

            RiscvRegister &write_reg = virt_real_reg_map[it->write_reg];
            auto getRealReg = [&](std::unique_ptr<std::vector<size_t *>> &regs,
                                  size_t ind) -> RiscvRegister & {
                return virt_real_reg_map[*(*regs)[ind]];
            };

            if (it->write_reg != 0) {
                switch (read_regs_length) {
                default:
                case 0:
                    snprintf(temp_buf, sizeof(temp_buf) - 1, it->inst.c_str(),
                             write_reg.getNameCString());
                    break;
                case 1:
                    if (strncmp("mv", it->inst.c_str(), 2) == 0 &&
                        write_reg == virt_real_reg_map[*(*it->read_regs)[0]]) {
                    }
                    snprintf(temp_buf, sizeof(temp_buf) - 1, it->inst.c_str(),
                             write_reg.getNameCString(),
                             getRealReg(it->read_regs, 0).getNameCString());
                    break;
                case 2:
                    snprintf(temp_buf, sizeof(temp_buf) - 1, it->inst.c_str(),
                             write_reg.getNameCString(),
                             getRealReg(it->read_regs, 0).getNameCString(),
                             getRealReg(it->read_regs, 1).getNameCString());
                    break;
                case 3:
                    snprintf(temp_buf, sizeof(temp_buf) - 1, it->inst.c_str(),
                             write_reg.getNameCString(),
                             getRealReg(it->read_regs, 0).getNameCString(),
                             getRealReg(it->read_regs, 1).getNameCString(),
                             getRealReg(it->read_regs, 2).getNameCString());
                    break;
                }
            } else {
                switch (read_regs_length) {
                case 0:
                    memcpy(temp_buf, it->inst.c_str(), it->inst.size());
                    break;
                case 1:
                    if (strncmp("mv", it->inst.c_str(), 2) == 0 &&
                        write_reg == virt_real_reg_map[*(*it->read_regs)[0]]) {
                    }
                    snprintf(temp_buf, sizeof(temp_buf) - 1, it->inst.c_str(),
                             getRealReg(it->read_regs, 0).getNameCString());
                    break;
                case 2:
                    snprintf(temp_buf, sizeof(temp_buf) - 1, it->inst.c_str(),
                             getRealReg(it->read_regs, 0).getNameCString(),
                             getRealReg(it->read_regs, 1).getNameCString());
                    break;
                case 3:
                    snprintf(temp_buf, sizeof(temp_buf) - 1, it->inst.c_str(),
                             getRealReg(it->read_regs, 0).getNameCString(),
                             getRealReg(it->read_regs, 1).getNameCString(),
                             getRealReg(it->read_regs, 2).getNameCString());
                    break;
                default:
                    break;
                }
            }

            snprintf(temp_buf_end, sizeof(temp_buf_end) - 1,
                     "\t%s\t\t\t# place: %ld\n", temp_buf, it->id);

            m_Inst_buff += temp_buf_end;
        }
    }

    for (auto &i : virt_reg_inst_stack) {
        if (!(i.true_inst || i.is_function_call)) {
            local_used_reg[start_ind] = virt_real_reg_map[i.write_reg];
            break;
        }
    }
    GetAvailableReg(local_used_reg[start_ind]);

    current_sp = origional_sp;
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
        size_t funcoffset = 8;
        std::stringstream ss(std::move(m_Inst_buff));
        m_Inst_buff.clear();
        char inst_buf[1024];
        while (ss.getline(inst_buf, 1023)) {
            if (strncmp(inst_buf, "return", 7) == 0) {
                char temp_buf[1024];
                snprintf(temp_buf, sizeof(temp_buf) - 1,
                         "\tlw ra, 0(s0)\n"
                         "\taddi sp, s0, %lu\n"
                         "\tlw s0, 4(s0)\n"
                         "\tjr ra\t\t\t\t# return\n",
                         funcoffset);
                m_Inst_buff += temp_buf;
            } else {
                m_Inst_buff += inst_buf;
                m_Inst_buff += '\n';
            }
        }

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
        function_argument_entry.emplace_back(const_cast<SymbolEntry *>(entry));

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
    function_used_reg.clear();
    current_sp = 0;
    std::string function_pre_return;

    m_context_stack.emplace(CodeGenContext::kFunction);
    m_symbol_manager.pushScope(
        std::move(m_symbol_table_of_scoping_nodes.at(&p_function)));

    std::string argument_inst_buf;
    auto &parameters = p_function.getParameters();
    function_arg_index = 0;
    for (auto &ast_node : parameters) {
        ast_node->accept(*this);
    };

    while (!m_Inst_stack.empty()) {
        argument_inst_buf += m_Inst_stack.top();
        m_Inst_stack.pop();
    }

    m_context_stack.emplace(CodeGenerator::CodeGenContext::kLocal);
    p_function.visitBodyChildNodes(*this);
    m_context_stack.pop();

    std::string pre_func;
    for (auto &reg : function_used_reg) {
        char buf[64];
        if (reg.saved_callee()) {
            snprintf(buf, 63, "\tlw %s, -%lu(s0)\n", reg.getNameCString(),
                     current_sp + 4);
            function_pre_return += buf;

            snprintf(buf, 63, "\tsw %s, -%lu(s0)\n", reg.getNameCString(),
                     current_sp + 4);
            pre_func += buf;

            current_sp += 4;
        }
    }

    dumpInstructions(m_output_file.get(), riscv_assembly_function_start_label,
                     p_function.getNameCString(), p_function.getNameCString(),
                     p_function.getNameCString());
    dumpInstructions(m_output_file.get(), riscv_assembly_add_stack_pointer,
                     (const size_t)current_sp);

    if (pre_func.size() > 0)
        dumpInstructions(m_output_file.get(), pre_func.c_str());

    dumpInstructions(m_output_file.get(), argument_inst_buf.c_str());

    std::stringstream ss(std::move(m_Inst_buff));
    m_Inst_buff.clear();
    char inst_buf[256];
    while (ss.getline(inst_buf, sizeof(inst_buf) - 1)) {
        if (strncmp(inst_buf, "return", 7) == 0) {
            char temp_buf[1024];
            snprintf(temp_buf, sizeof(temp_buf) - 1,
                     "\tlw ra, 0(s0)\n"
                     "\taddi sp, s0, 8\n"
                     "\tlw s0, 4(s0)\n"
                     "\tjr ra\t\t\t\t# return\n");
            m_Inst_buff += function_pre_return;
            m_Inst_buff += temp_buf;
        } else {
            m_Inst_buff += inst_buf;
            m_Inst_buff += '\n';
        }
    }

    dumpInstructions(m_output_file.get(), m_Inst_buff.c_str());
    m_Inst_buff.clear();

    // Remove the entries in the hash table
    m_symbol_manager.popScope();
    m_context_stack.pop();

    dumpInstructions(m_output_file.get(), riscv_assembly_reset_stack_pointer,
                     current_sp);
    dumpInstructions(m_output_file.get(), function_pre_return.c_str());
    dumpInstructions(m_output_file.get(), riscv_assembly_function_end,
                     p_function.getNameCString(), p_function.getNameCString());
    current_sp = prev_sp;
}

void CodeGenerator::visit(CompoundStatementNode &p_compound_statement) {
    // Reconstruct the scope for looking up the symbol entry.
    auto visit_ast_node = [&](auto &ast_node) { ast_node->accept(*this); };
    auto prev_sp = current_sp;
    bool is_for_loop = m_context_stack.top() == CodeGenContext::kForLoopIfWhile;
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
    size_t curr_ind = ThreeAddressCodeTable.size();
    ThreeAddressCodeTable.emplace_back(
        (ThreeAddressCodeFuncInvocation){.func = &p_func_invocation});

    std::vector<size_t> parameters;
    std::for_each(p_func_invocation.getArguments().begin(),
                  p_func_invocation.getArguments().end(),
                  [&](const std::unique_ptr<ExpressionNode> &p_expr) {
                      const_cast<ExpressionNode &>(*p_expr).accept(*this);
                      parameters.emplace_back(three_addr_ind);
                  });

    std::get<ThreeAddressCodeFuncInvocation>(ThreeAddressCodeTable[curr_ind])
        .parameters = std::move(parameters);
    three_addr_ind = curr_ind;
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
    std::string prev_inst_buf = std::move(m_Inst_buff);
    m_Inst_buff.clear();
    m_context_stack.emplace(CodeGenContext::kForLoopIfWhile);

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
    m_Inst_buff = std::move(prev_inst_buf) + m_Inst_buff;
    m_context_stack.pop();
}

void CodeGenerator::visit(WhileNode &p_while) {
    std::string prev_inst_buf = std::move(m_Inst_buff);
    m_Inst_buff.clear();

    long l1 = BranchLabel, l2 = BranchLabel + 1, l3 = BranchLabel + 2;
    BranchLabel += 3;
    char inst_buf_c_str[1024];
    m_context_stack.emplace(CodeGenContext::kForLoopIfWhile);

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
    m_Inst_buff = std::move(prev_inst_buf) + m_Inst_buff;
    m_context_stack.pop();
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
    m_Inst_buff.clear();

    auto const &upper = p_for.getUpperBound();

    m_context_stack.emplace(CodeGenContext::kForLoopIfWhile);
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
    m_Inst_buff = std::move(prev_inst_buf) + std::move(inst_buf);
}

void CodeGenerator::visit(ReturnNode &p_return) {
    p_return.visitChildNodes(*this);

    // return value
    auto local_used_reg = expr_handler(0, RiscvRegisterEnum::a0);
    char buf[1024];
    snprintf(buf, 63, "return\n");
    m_Inst_buff += std::move(buf);

    std::for_each(local_used_reg.begin(), local_used_reg.end(),
                  [&](auto &reg) { ReturnReg(reg); });
}
