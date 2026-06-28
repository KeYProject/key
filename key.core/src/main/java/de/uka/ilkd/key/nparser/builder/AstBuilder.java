/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.builder;

import de.uka.ilkd.key.nparser.JavaKeYParser;
import de.uka.ilkd.key.util.parsing.BuildingException;
import de.uka.ilkd.key.util.parsing.BuildingIssue;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RuleContext;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.key_project.key.ast.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;
import java.util.stream.Collectors;

/**
 * This class brings some nice features to the visitors of key's ast.
 *
 * <ul>
 * <li>It makes casting implicit by using {{@link #accept(RuleContext)}}
 * <li>It allows to pass arguments by an explicit stack.
 * <li>It brings handling of errors and warnings.
 * </ul>
 *
 * @author Alexander Weigl
 */
@SuppressWarnings("unchecked")
abstract class AstBuilder extends AbstractBuilder<AstNode> {
    @Override
    public AstNode visitAbbreviation(JavaKeYParser.AbbreviationContext ctx) {
        return super.visitAbbreviation(ctx);
    }

    @Override
    public AstNode visitAccessterm(JavaKeYParser.AccesstermContext ctx) {
        return super.visitAccessterm(ctx);
    }

    @Override
    public AstNode visitActivated_choice(JavaKeYParser.Activated_choiceContext ctx) {
        return super.visitActivated_choice(ctx);
    }

    @Override
    public AstNode visitAdd(JavaKeYParser.AddContext ctx) {
        return super.visitAdd(ctx);
    }

    @Override
    public AstNode visitAddprogvar(JavaKeYParser.AddprogvarContext ctx) {
        return super.visitAddprogvar(ctx);
    }

    @Override
    public AstNode visitAddrules(JavaKeYParser.AddrulesContext ctx) {
        return super.visitAddrules(ctx);
    }

    @Override
    public AstNode visitArg_sorts(JavaKeYParser.Arg_sortsContext ctx) {
        return super.visitArg_sorts(ctx);
    }

    @Override
    public AstNode visitArg_sorts_or_formula(JavaKeYParser.Arg_sorts_or_formulaContext ctx) {
        return super.visitArg_sorts_or_formula(ctx);
    }

    @Override
    public AstNode visitArg_sorts_or_formula_helper(JavaKeYParser.Arg_sorts_or_formula_helperContext ctx) {
        return super.visitArg_sorts_or_formula_helper(ctx);
    }

    @Override
    public AstNode visitArgument_list(JavaKeYParser.Argument_listContext ctx) {
        return super.visitArgument_list(ctx);
    }

    @Override
    public AstNode visitArrayopid(JavaKeYParser.ArrayopidContext ctx) {
        return super.visitArrayopid(ctx);
    }

    @Override
    public AstNode visitAtom_prefix(JavaKeYParser.Atom_prefixContext ctx) {
        return super.visitAtom_prefix(ctx);
    }

    @Override
    public AstNode visitAttribute_complex(JavaKeYParser.Attribute_complexContext ctx) {
        return super.visitAttribute_complex(ctx);
    }

    @Override
    public AstNode visitAttribute_simple(JavaKeYParser.Attribute_simpleContext ctx) {
        return super.visitAttribute_simple(ctx);
    }

    @Override
    public AstNode visitAttribute_star(JavaKeYParser.Attribute_starContext ctx) {
        return super.visitAttribute_star(ctx);
    }

    @Override
    public AstNode visitBoolean_literal(JavaKeYParser.Boolean_literalContext ctx) {
        return super.visitBoolean_literal(ctx);
    }

    @Override
    public AstNode visitBootClassPath(JavaKeYParser.BootClassPathContext ctx) {
        return super.visitBootClassPath(ctx);
    }

    @Override
    public AstNode visitBound_variables(JavaKeYParser.Bound_variablesContext ctx) {
        return super.visitBound_variables(ctx);
    }

    @Override
    public AstNode visitBracket_access_heap_term(JavaKeYParser.Bracket_access_heap_termContext ctx) {
        return super.visitBracket_access_heap_term(ctx);
    }

    @Override
    public AstNode visitBracket_access_heap_update(JavaKeYParser.Bracket_access_heap_updateContext ctx) {
        return super.visitBracket_access_heap_update(ctx);
    }

    @Override
    public AstNode visitBracket_access_indexrange(JavaKeYParser.Bracket_access_indexrangeContext ctx) {
        return super.visitBracket_access_indexrange(ctx);
    }

    @Override
    public AstNode visitBracket_access_star(JavaKeYParser.Bracket_access_starContext ctx) {
        return super.visitBracket_access_star(ctx);
    }

    @Override
    public AstNode visitBracket_suffix_heap(JavaKeYParser.Bracket_suffix_heapContext ctx) {
        return super.visitBracket_suffix_heap(ctx);
    }

    @Override
    public AstNode visitBracket_term(JavaKeYParser.Bracket_termContext ctx) {
        return super.visitBracket_term(ctx);
    }

    @Override
    public AstNode visitCall(JavaKeYParser.CallContext ctx) {
        return super.visitCall(ctx);
    }

    @Override
    public AstNode visitCast_term(JavaKeYParser.Cast_termContext ctx) {
        return super.visitCast_term(ctx);
    }

    @Override
    public AstNode visitCbool(JavaKeYParser.CboolContext ctx) {
        return super.visitCbool(ctx);
    }

    @Override
    public AstNode visitCfile(JavaKeYParser.CfileContext ctx) {
        return super.visitCfile(ctx);
    }

    @Override
    public AstNode visitCfpd(JavaKeYParser.CfpdContext ctx) {
        return super.visitCfpd(ctx);
    }

    @Override
    public AstNode visitCfpf(JavaKeYParser.CfpfContext ctx) {
        return super.visitCfpf(ctx);
    }

    @Override
    public AstNode visitCfpr(JavaKeYParser.CfprContext ctx) {
        return super.visitCfpr(ctx);
    }

    @Override
    public AstNode visitChar_literal(JavaKeYParser.Char_literalContext ctx) {
        return super.visitChar_literal(ctx);
    }

    @Override
    public AstNode visitChoice(JavaKeYParser.ChoiceContext ctx) {
        return super.visitChoice(ctx);
    }

    @Override
    public AstNode visitCintb(JavaKeYParser.CintbContext ctx) {
        return super.visitCintb(ctx);
    }

    @Override
    public AstNode visitCintd(JavaKeYParser.CintdContext ctx) {
        return super.visitCintd(ctx);
    }

    @Override
    public AstNode visitCinth(JavaKeYParser.CinthContext ctx) {
        return super.visitCinth(ctx);
    }

    @Override
    public AstNode visitCkey(JavaKeYParser.CkeyContext ctx) {
        return super.visitCkey(ctx);
    }

    @Override
    public AstNode visitCkv(JavaKeYParser.CkvContext ctx) {
        return super.visitCkv(ctx);
    }

    @Override
    public AstNode visitClassPaths(JavaKeYParser.ClassPathsContext ctx) {
        return super.visitClassPaths(ctx);
    }

    @Override
    public AstNode visitComparison_term(JavaKeYParser.Comparison_termContext ctx) {
        return super.visitComparison_term(ctx);
    }

    @Override
    public AstNode visitConjunction_term(JavaKeYParser.Conjunction_termContext ctx) {
        return super.visitConjunction_term(ctx);
    }

    @Override
    public AstNode visitContracts(JavaKeYParser.ContractsContext ctx) {
        return super.visitContracts(ctx);
    }

    @Override
    public AstNode visitCstring(JavaKeYParser.CstringContext ctx) {
        return super.visitCstring(ctx);
    }

    @Override
    public AstNode visitCsymbol(JavaKeYParser.CsymbolContext ctx) {
        return super.visitCsymbol(ctx);
    }

    @Override
    public AstNode visitDatatype_constructor(JavaKeYParser.Datatype_constructorContext ctx) {
        return super.visitDatatype_constructor(ctx);
    }

    @Override
    public AstNode visitDatatype_decl(JavaKeYParser.Datatype_declContext ctx) {
        return super.visitDatatype_decl(ctx);
    }

    @Override
    public AstNode visitDatatype_decls(JavaKeYParser.Datatype_declsContext ctx) {
        return super.visitDatatype_decls(ctx);
    }

    @Override
    public AstNode visitDecls(JavaKeYParser.DeclsContext ctx) {
        return super.visitDecls(ctx);
    }

    @Override
    public AstNode visitDisjunction_term(JavaKeYParser.Disjunction_termContext ctx) {
        return super.visitDisjunction_term(ctx);
    }

    @Override
    public AstNode visitDoubleLiteral(JavaKeYParser.DoubleLiteralContext ctx) {
        return super.visitDoubleLiteral(ctx);
    }

    @Override
    public AstNode visitElementary_update_term(JavaKeYParser.Elementary_update_termContext ctx) {
        return super.visitElementary_update_term(ctx);
    }

    @Override
    public AstNode visitEmptyset(JavaKeYParser.EmptysetContext ctx) {
        return super.visitEmptyset(ctx);
    }

    @Override
    public AstNode visitEquality_term(JavaKeYParser.Equality_termContext ctx) {
        return super.visitEquality_term(ctx);
    }

    @Override
    public AstNode visitEquivalence_term(JavaKeYParser.Equivalence_termContext ctx) {
        return super.visitEquivalence_term(ctx);
    }

    @Override
    public AstNode visitExtends_sorts(JavaKeYParser.Extends_sortsContext ctx) {
        return super.visitExtends_sorts(ctx);
    }

    @Override
    public AstNode visitFile(JavaKeYParser.FileContext ctx) {
        List<String> docComments = visit(ctx.DOC_COMMENT());
        Profile profile = accept(ctx.profile());
        Preferences preferences = accept(ctx.preferences());
        List<Declaration> decls = accept(ctx.decls());
        Problem problem = accept(ctx.problem());
        Proof proof = accept(ctx.proof());
        Position position = getPosition();
        return new File(docComments, profile, preferences, decls, problem, proof, position);
    }

    @Override
    public AstNode visitFloatLiteral(JavaKeYParser.FloatLiteralContext ctx) {
        return super.visitFloatLiteral(ctx);
    }

    @Override
    public AstNode visitFormal_sort_args(JavaKeYParser.Formal_sort_argsContext ctx) {
        return super.visitFormal_sort_args(ctx);
    }

    @Override
    public AstNode visitFormal_sort_param_decl(JavaKeYParser.Formal_sort_param_declContext ctx) {
        return super.visitFormal_sort_param_decl(ctx);
    }

    @Override
    public AstNode visitFormal_sort_param_decls(JavaKeYParser.Formal_sort_param_declsContext ctx) {
        return super.visitFormal_sort_param_decls(ctx);
    }

    @Override
    public AstNode visitFunc_decl(JavaKeYParser.Func_declContext ctx) {
        return super.visitFunc_decl(ctx);
    }

    @Override
    public AstNode visitFunc_decls(JavaKeYParser.Func_declsContext ctx) {
        return super.visitFunc_decls(ctx);
    }

    @Override
    public AstNode visitFuncpred_name(JavaKeYParser.Funcpred_nameContext ctx) {
        return super.visitFuncpred_name(ctx);
    }

    @Override
    public AstNode visitGoalspec(JavaKeYParser.GoalspecContext ctx) {
        return super.visitGoalspec(ctx);
    }

    @Override
    public AstNode visitGoalspecs(JavaKeYParser.GoalspecsContext ctx) {
        return super.visitGoalspecs(ctx);
    }

    @Override
    public AstNode visitGoalspecwithoption(JavaKeYParser.GoalspecwithoptionContext ctx) {
        return super.visitGoalspecwithoption(ctx);
    }

    @Override
    public AstNode visitId_declaration(JavaKeYParser.Id_declarationContext ctx) {
        return super.visitId_declaration(ctx);
    }

    @Override
    public AstNode visitIfExThenElseTerm(JavaKeYParser.IfExThenElseTermContext ctx) {
        return super.visitIfExThenElseTerm(ctx);
    }

    @Override
    public AstNode visitIfThenElseTerm(JavaKeYParser.IfThenElseTermContext ctx) {
        return super.visitIfThenElseTerm(ctx);
    }

    @Override
    public AstNode visitImplication_term(JavaKeYParser.Implication_termContext ctx) {
        return super.visitImplication_term(ctx);
    }

    @Override
    public AstNode visitInteger(JavaKeYParser.IntegerContext ctx) {
        return super.visitInteger(ctx);
    }

    @Override
    public AstNode visitInvariants(JavaKeYParser.InvariantsContext ctx) {
        return super.visitInvariants(ctx);
    }

    @Override
    public AstNode visitLabel(JavaKeYParser.LabelContext ctx) {
        return super.visitLabel(ctx);
    }

    @Override
    public AstNode visitList(JavaKeYParser.ListContext ctx) {
        return super.visitList(ctx);
    }

    @Override
    public AstNode visitLiterals(JavaKeYParser.LiteralsContext ctx) {
        return super.visitLiterals(ctx);
    }

    @Override
    public AstNode visitLocation_term(JavaKeYParser.Location_termContext ctx) {
        return super.visitLocation_term(ctx);
    }

    @Override
    public AstNode visitLocset_term(JavaKeYParser.Locset_termContext ctx) {
        return super.visitLocset_term(ctx);
    }

    @Override
    public AstNode visitMetaId(JavaKeYParser.MetaIdContext ctx) {
        return super.visitMetaId(ctx);
    }

    @Override
    public AstNode visitMetaTerm(JavaKeYParser.MetaTermContext ctx) {
        return super.visitMetaTerm(ctx);
    }

    @Override
    public AstNode visitModality_term(JavaKeYParser.Modality_termContext ctx) {
        return super.visitModality_term(ctx);
    }

    @Override
    public AstNode visitModifiers(JavaKeYParser.ModifiersContext ctx) {
        return super.visitModifiers(ctx);
    }

    @Override
    public AstNode visitNegation_term(JavaKeYParser.Negation_termContext ctx) {
        return super.visitNegation_term(ctx);
    }

    @Override
    public AstNode visitOne_bound_variable(JavaKeYParser.One_bound_variableContext ctx) {
        return super.visitOne_bound_variable(ctx);
    }

    @Override
    public AstNode visitOne_contract(JavaKeYParser.One_contractContext ctx) {
        return super.visitOne_contract(ctx);
    }

    @Override
    public AstNode visitOne_include(JavaKeYParser.One_includeContext ctx) {
        return super.visitOne_include(ctx);
    }

    @Override
    public AstNode visitOne_include_statement(JavaKeYParser.One_include_statementContext ctx) {
        return super.visitOne_include_statement(ctx);
    }

    @Override
    public AstNode visitOne_invariant(JavaKeYParser.One_invariantContext ctx) {
        return super.visitOne_invariant(ctx);
    }

    @Override
    public AstNode visitOne_schema_modal_op_decl(JavaKeYParser.One_schema_modal_op_declContext ctx) {
        return super.visitOne_schema_modal_op_decl(ctx);
    }

    @Override
    public AstNode visitOne_schema_var_decl(JavaKeYParser.One_schema_var_declContext ctx) {
        return super.visitOne_schema_var_decl(ctx);
    }

    @Override
    public AstNode visitOne_sort_decl(JavaKeYParser.One_sort_declContext ctx) {
        return super.visitOne_sort_decl(ctx);
    }

    @Override
    public AstNode visitOneof_sorts(JavaKeYParser.Oneof_sortsContext ctx) {
        return super.visitOneof_sorts(ctx);
    }

    @Override
    public AstNode visitOneProgramSource(JavaKeYParser.OneProgramSourceContext ctx) {
        return super.visitOneProgramSource(ctx);
    }

    @Override
    public AstNode visitOption(JavaKeYParser.OptionContext ctx) {
        return super.visitOption(ctx);
    }

    @Override
    public AstNode visitOption_decls(JavaKeYParser.Option_declsContext ctx) {
        return super.visitOption_decls(ctx);
    }

    @Override
    public AstNode visitOption_expr_and(JavaKeYParser.Option_expr_andContext ctx) {
        return super.visitOption_expr_and(ctx);
    }

    @Override
    public AstNode visitOption_expr_not(JavaKeYParser.Option_expr_notContext ctx) {
        return super.visitOption_expr_not(ctx);
    }

    @Override
    public AstNode visitOption_expr_or(JavaKeYParser.Option_expr_orContext ctx) {
        return super.visitOption_expr_or(ctx);
    }

    @Override
    public AstNode visitOption_expr_paren(JavaKeYParser.Option_expr_parenContext ctx) {
        return super.visitOption_expr_paren(ctx);
    }

    @Override
    public AstNode visitOption_expr_prop(JavaKeYParser.Option_expr_propContext ctx) {
        return super.visitOption_expr_prop(ctx);
    }

    @Override
    public AstNode visitOption_list(JavaKeYParser.Option_listContext ctx) {
        return super.visitOption_list(ctx);
    }

    @Override
    public AstNode visitOptionDecl(JavaKeYParser.OptionDeclContext ctx) {
        return super.visitOptionDecl(ctx);
    }

    @Override
    public AstNode visitOptions_choice(JavaKeYParser.Options_choiceContext ctx) {
        return super.visitOptions_choice(ctx);
    }

    @Override
    public AstNode visitParallel_term(JavaKeYParser.Parallel_termContext ctx) {
        return super.visitParallel_term(ctx);
    }

    @Override
    public AstNode visitParametric_sort_decl(JavaKeYParser.Parametric_sort_declContext ctx) {
        return super.visitParametric_sort_decl(ctx);
    }

    @Override
    public AstNode visitPred_decl(JavaKeYParser.Pred_declContext ctx) {
        return super.visitPred_decl(ctx);
    }

    @Override
    public AstNode visitPred_decls(JavaKeYParser.Pred_declsContext ctx) {
        return super.visitPred_decls(ctx);
    }

    @Override
    public AstNode visitPreferences(JavaKeYParser.PreferencesContext ctx) {
        return super.visitPreferences(ctx);
    }

    @Override
    public AstNode visitPrimitive_labeled_term(JavaKeYParser.Primitive_labeled_termContext ctx) {
        return super.visitPrimitive_labeled_term(ctx);
    }

    @Override
    public AstNode visitPrimitive_term(JavaKeYParser.Primitive_termContext ctx) {
        return super.visitPrimitive_term(ctx);
    }

    @Override
    public AstNode visitProblem(JavaKeYParser.ProblemContext ctx) {
        return new Problem(accept(ctx.name), createPosition(ctx));
    }

    @Override
    public AstNode visitProfile(JavaKeYParser.ProfileContext ctx) {
        return new Profile(accept(ctx.name), createPosition(ctx));
    }

    private @Nullable Position createPosition(ParserRuleContext ctx) {
        return null;
    }

    @Override
    public AstNode visitProg_var_decls(JavaKeYParser.Prog_var_declsContext ctx) {
        return super.visitProg_var_decls(ctx);
    }

    @Override
    public AstNode visitProgramSource(JavaKeYParser.ProgramSourceContext ctx) {
        return super.visitProgramSource(ctx);
    }

    @Override
    public AstNode visitProof(JavaKeYParser.ProofContext ctx) {
        return super.visitProof(ctx);
    }

    @Override
    public AstNode visitProofScript(JavaKeYParser.ProofScriptContext ctx) {
        return super.visitProofScript(ctx);
    }

    @Override
    public AstNode visitProofScriptCodeBlock(JavaKeYParser.ProofScriptCodeBlockContext ctx) {
        return super.visitProofScriptCodeBlock(ctx);
    }

    @Override
    public AstNode visitProofScriptCommand(JavaKeYParser.ProofScriptCommandContext ctx) {
        return super.visitProofScriptCommand(ctx);
    }

    @Override
    public AstNode visitProofScriptEntry(JavaKeYParser.ProofScriptEntryContext ctx) {
        return super.visitProofScriptEntry(ctx);
    }

    @Override
    public AstNode visitProofScriptEOF(JavaKeYParser.ProofScriptEOFContext ctx) {
        return super.visitProofScriptEOF(ctx);
    }

    @Override
    public AstNode visitProofScriptExpression(JavaKeYParser.ProofScriptExpressionContext ctx) {
        return super.visitProofScriptExpression(ctx);
    }

    @Override
    public AstNode visitProofScriptParameter(JavaKeYParser.ProofScriptParameterContext ctx) {
        return super.visitProofScriptParameter(ctx);
    }

    @Override
    public AstNode visitProofScriptParameterName(JavaKeYParser.ProofScriptParameterNameContext ctx) {
        return super.visitProofScriptParameterName(ctx);
    }

    @Override
    public AstNode visitProofScriptParameters(JavaKeYParser.ProofScriptParametersContext ctx) {
        return super.visitProofScriptParameters(ctx);
    }

    @Override
    public AstNode visitPvset(JavaKeYParser.PvsetContext ctx) {
        return super.visitPvset(ctx);
    }

    @Override
    public AstNode visitQuantifierterm(JavaKeYParser.QuantifiertermContext ctx) {
        return super.visitQuantifierterm(ctx);
    }

    @Override
    public AstNode visitRealLiteral(JavaKeYParser.RealLiteralContext ctx) {
        return super.visitRealLiteral(ctx);
    }

    @Override
    public AstNode visitReplacewith(JavaKeYParser.ReplacewithContext ctx) {
        return super.visitReplacewith(ctx);
    }

    @Override
    public AstNode visitRuleset(JavaKeYParser.RulesetContext ctx) {
        return super.visitRuleset(ctx);
    }

    @Override
    public AstNode visitRuleset_decls(JavaKeYParser.Ruleset_declsContext ctx) {
        return super.visitRuleset_decls(ctx);
    }

    @Override
    public AstNode visitRulesets(JavaKeYParser.RulesetsContext ctx) {
        return super.visitRulesets(ctx);
    }

    @Override
    public AstNode visitRulesOrAxioms(JavaKeYParser.RulesOrAxiomsContext ctx) {
        return super.visitRulesOrAxioms(ctx);
    }

    @Override
    public AstNode visitSchema_modifiers(JavaKeYParser.Schema_modifiersContext ctx) {
        return super.visitSchema_modifiers(ctx);
    }

    @Override
    public AstNode visitSchema_var_decls(JavaKeYParser.Schema_var_declsContext ctx) {
        return super.visitSchema_var_decls(ctx);
    }

    @Override
    public AstNode visitSemisequent(JavaKeYParser.SemisequentContext ctx) {
        return super.visitSemisequent(ctx);
    }

    @Override
    public AstNode visitSeq(JavaKeYParser.SeqContext ctx) {
        return super.visitSeq(ctx);
    }

    @Override
    public AstNode visitSeqEOF(JavaKeYParser.SeqEOFContext ctx) {
        return super.visitSeqEOF(ctx);
    }

    @Override
    public AstNode visitSimple_ident(JavaKeYParser.Simple_identContext ctx) {
        return super.visitSimple_ident(ctx);
    }

    @Override
    public AstNode visitSimple_ident_comma_list(JavaKeYParser.Simple_ident_comma_listContext ctx) {
        return super.visitSimple_ident_comma_list(ctx);
    }

    @Override
    public AstNode visitSimple_ident_comma_list_with_docs(JavaKeYParser.Simple_ident_comma_list_with_docsContext ctx) {
        return super.visitSimple_ident_comma_list_with_docs(ctx);
    }

    @Override
    public AstNode visitSimple_ident_dots(JavaKeYParser.Simple_ident_dotsContext ctx) {
        return super.visitSimple_ident_dots(ctx);
    }

    @Override
    public AstNode visitSimple_ident_dots_comma_list(JavaKeYParser.Simple_ident_dots_comma_listContext ctx) {
        return super.visitSimple_ident_dots_comma_list(ctx);
    }

    @Override
    public AstNode visitSimple_ident_dots_comma_list_with_docs(JavaKeYParser.Simple_ident_dots_comma_list_with_docsContext ctx) {
        return super.visitSimple_ident_dots_comma_list_with_docs(ctx);
    }

    @Override
    public AstNode visitSimple_ident_dots_with_docs(JavaKeYParser.Simple_ident_dots_with_docsContext ctx) {
        return super.visitSimple_ident_dots_with_docs(ctx);
    }

    @Override
    public AstNode visitSimple_ident_with_doc(JavaKeYParser.Simple_ident_with_docContext ctx) {
        return super.visitSimple_ident_with_doc(ctx);
    }

    @Override
    public AstNode visitSingle_label(JavaKeYParser.Single_labelContext ctx) {
        return super.visitSingle_label(ctx);
    }

    @Override
    public AstNode visitSort_decls(JavaKeYParser.Sort_declsContext ctx) {
        return super.visitSort_decls(ctx);
    }

    @Override
    public AstNode visitSortId(JavaKeYParser.SortIdContext ctx) {
        return super.visitSortId(ctx);
    }

    @Override
    public AstNode visitString_literal(JavaKeYParser.String_literalContext ctx) {
        return super.visitString_literal(ctx);
    }

    @Override
    public AstNode visitString_value(JavaKeYParser.String_valueContext ctx) {
        return super.visitString_value(ctx);
    }

    @Override
    public AstNode visitStrong_arith_term_1(JavaKeYParser.Strong_arith_term_1Context ctx) {
        return super.visitStrong_arith_term_1(ctx);
    }

    @Override
    public AstNode visitStrong_arith_term_2(JavaKeYParser.Strong_arith_term_2Context ctx) {
        return super.visitStrong_arith_term_2(ctx);
    }

    @Override
    public AstNode visitSubstitution_term(JavaKeYParser.Substitution_termContext ctx) {
        return super.visitSubstitution_term(ctx);
    }

    @Override
    public AstNode visitTable(JavaKeYParser.TableContext ctx) {
        return super.visitTable(ctx);
    }

    @Override
    public AstNode visitTaclet(JavaKeYParser.TacletContext ctx) {
        return super.visitTaclet(ctx);
    }

    @Override
    public AstNode visitTacletlist(JavaKeYParser.TacletlistContext ctx) {
        return super.visitTacletlist(ctx);
    }

    @Override
    public AstNode visitTerm(JavaKeYParser.TermContext ctx) {
        return super.visitTerm(ctx);
    }

    @Override
    public AstNode visitTerm60(JavaKeYParser.Term60Context ctx) {
        return super.visitTerm60(ctx);
    }

    @Override
    public AstNode visitTermEOF(JavaKeYParser.TermEOFContext ctx) {
        return super.visitTermEOF(ctx);
    }

    @Override
    public AstNode visitTermorseq(JavaKeYParser.TermorseqContext ctx) {
        return super.visitTermorseq(ctx);
    }

    @Override
    public AstNode visitTermParen(JavaKeYParser.TermParenContext ctx) {
        return super.visitTermParen(ctx);
    }

    @Override
    public AstNode visitTransform_decl(JavaKeYParser.Transform_declContext ctx) {
        return super.visitTransform_decl(ctx);
    }

    @Override
    public AstNode visitTransform_decls(JavaKeYParser.Transform_declsContext ctx) {
        return super.visitTransform_decls(ctx);
    }

    @Override
    public AstNode visitTriggers(JavaKeYParser.TriggersContext ctx) {
        return super.visitTriggers(ctx);
    }

    @Override
    public AstNode visitTypemapping(JavaKeYParser.TypemappingContext ctx) {
        return super.visitTypemapping(ctx);
    }

    @Override
    public AstNode visitUnary_minus_term(JavaKeYParser.Unary_minus_termContext ctx) {
        return super.visitUnary_minus_term(ctx);
    }

    @Override
    public AstNode visitUpdate_term(JavaKeYParser.Update_termContext ctx) {
        return super.visitUpdate_term(ctx);
    }

    @Override
    public AstNode visitVarexp(JavaKeYParser.VarexpContext ctx) {
        return super.visitVarexp(ctx);
    }

    @Override
    public AstNode visitVarexp_argument(JavaKeYParser.Varexp_argumentContext ctx) {
        return super.visitVarexp_argument(ctx);
    }

    @Override
    public AstNode visitVarexpId(JavaKeYParser.VarexpIdContext ctx) {
        return super.visitVarexpId(ctx);
    }

    @Override
    public AstNode visitVarexplist(JavaKeYParser.VarexplistContext ctx) {
        return super.visitVarexplist(ctx);
    }

    @Override
    public AstNode visitVarId(JavaKeYParser.VarIdContext ctx) {
        return super.visitVarId(ctx);
    }

    @Override
    public AstNode visitVarIds(JavaKeYParser.VarIdsContext ctx) {
        return super.visitVarIds(ctx);
    }

    @Override
    public AstNode visitWeak_arith_term(JavaKeYParser.Weak_arith_termContext ctx) {
        return super.visitWeak_arith_term(ctx);
    }

    @Override
    public AstNode visitWhere_to_bind(JavaKeYParser.Where_to_bindContext ctx) {
        return super.visitWhere_to_bind(ctx);
    }
}
