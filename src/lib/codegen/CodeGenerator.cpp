#include "codegen/CodeGenerator.hpp"
#include "AST/CompoundStatement.hpp"
#include "AST/for.hpp"
#include "AST/function.hpp"
#include "AST/program.hpp"
#include "sema/SemanticAnalyzer.hpp"
#include "sema/SymbolTable.hpp"
#include "visitor/AstNodeInclude.hpp"

#include <algorithm>
#include <cassert>
#include <cstdarg>
#include <cstdio>
#include <memory>
#include <string>
#include <unordered_map>
#include <utility>

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

    constexpr const char *const riscv_assembly_global_uninitialized =
        ".section   .bss";

    auto visit_ast_node = [&](auto &ast_node) { ast_node->accept(*this); };
    for_each(p_program.getDeclNodes().begin(), p_program.getDeclNodes().end(),
             visit_ast_node);
    for_each(p_program.getFuncNodes().begin(), p_program.getFuncNodes().end(),
             visit_ast_node);

    constexpr const char *const riscv_assembly_main_func_begin =
        ".section    .text\n"
        "    .align 2\n"
        "    .globl main          # emit symbol 'main' to the global symbol "
        "table\n"
        "    .type main, @function\n"
        "main:\n";

    dumpInstructions(m_output_file.get(), riscv_assembly_main_func_begin);

    const_cast<CompoundStatementNode &>(p_program.getBody()).accept(*this);

    constexpr const char *const riscv_assembly_main_func_end =
        "    add a0, x0, x0     # return 0 at the end\n"
        "    jr ra\n"
        "    .size main, .-main";

    dumpInstructions(m_output_file.get(), riscv_assembly_main_func_end);

    m_symbol_manager.popScope();
    m_context_stack.pop();
}

void CodeGenerator::visit(DeclNode &p_decl) {
    p_decl.visitChildNodes(*this);
}

void CodeGenerator::visit(VariableNode &p_variable) {
    auto entry = m_symbol_manager.addSymbol(
        p_variable.getName(), determineVarKind(p_variable),
        p_variable.getTypePtr(), p_variable.getConstantPtr());
    p_variable.visitChildNodes(*this);
}

void CodeGenerator::visit(ConstantValueNode &p_constant_value) {}

void CodeGenerator::visit(FunctionNode &p_function) {
    // Reconstruct the scope for looking up the symbol entry.
    m_symbol_manager.pushScope(
        std::move(m_symbol_table_of_scoping_nodes.at(&p_function)));

    p_function.visitChildNodes(*this);

    // Remove the entries in the hash table
    m_symbol_manager.popScope();
}

void CodeGenerator::visit(CompoundStatementNode &p_compound_statement) {
    // Reconstruct the scope for looking up the symbol entry.
    m_symbol_manager.pushScope(
        std::move(m_symbol_table_of_scoping_nodes.at(&p_compound_statement)));

    p_compound_statement.visitChildNodes(*this);

    m_symbol_manager.popScope();
}

void CodeGenerator::visit(PrintNode &p_print) {}

void CodeGenerator::visit(BinaryOperatorNode &p_bin_op) {}

void CodeGenerator::visit(UnaryOperatorNode &p_un_op) {}

void CodeGenerator::visit(FunctionInvocationNode &p_func_invocation) {}

void CodeGenerator::visit(VariableReferenceNode &p_variable_ref) {}

void CodeGenerator::visit(AssignmentNode &p_assignment) {}

void CodeGenerator::visit(ReadNode &p_read) {}

void CodeGenerator::visit(IfNode &p_if) {}

void CodeGenerator::visit(WhileNode &p_while) {}

void CodeGenerator::visit(ForNode &p_for) {
    // Reconstruct the scope for looking up the symbol entry.
    m_symbol_manager.pushScope(
        std::move(m_symbol_table_of_scoping_nodes.at(&p_for)));

    p_for.visitChildNodes(*this);

    // Remove the entries in the hash table
    m_symbol_manager.popScope();
}

void CodeGenerator::visit(ReturnNode &p_return) {}
