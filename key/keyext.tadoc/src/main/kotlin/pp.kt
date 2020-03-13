package org.key_project.core.doc

import de.uka.ilkd.key.nparser.KeYLexer
import de.uka.ilkd.key.nparser.KeYParser
import de.uka.ilkd.key.nparser.KeYParserBaseVisitor
import org.antlr.v4.runtime.tree.TerminalNode

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/12/20)
 */
class PrettyPrinter(val index: Index) : KeYParserBaseVisitor<String>() {
    private val printReferences = true
    val tokenSymbols = index.map { (a, b) -> b }.filterIsInstance<Symbol.Token>()

    override fun aggregateResult(aggregate: String?, nextResult: String?) =
            (aggregate ?: "") + (nextResult ?: "")

    override fun visitTerminal(node: TerminalNode): String {
        val t = node.symbol
        val text = t.text
        if (t.type == KeYLexer.DOC_COMMENT) return ""
        if (!printReferences) return "$text "
        val s = tokenSymbols.find { it.tokenType == t.type }
        return if (s != null)
            "<a class=\"token\" href=\"${s.href}\">$text</a> "
        else
            "$text "
    }

    override fun defaultResult(): String {
        return ""
    }

    override fun visitProblem(ctx: KeYParser.ProblemContext?): String {
        return super.visitProblem(ctx)
    }

    override fun visitOne_include_statement(ctx: KeYParser.One_include_statementContext?): String {
        return super.visitOne_include_statement(ctx)
    }

    override fun visitOne_include(ctx: KeYParser.One_includeContext?): String {
        return super.visitOne_include(ctx)
    }

    override fun visitOptions_choice(ctx: KeYParser.Options_choiceContext?): String {
        return super.visitOptions_choice(ctx)
    }

    override fun visitActivated_choice(ctx: KeYParser.Activated_choiceContext?): String {
        return super.visitActivated_choice(ctx)
    }

    override fun visitOption_decls(ctx: KeYParser.Option_declsContext?): String {
        return super.visitOption_decls(ctx)
    }

    override fun visitChoice(ctx: KeYParser.ChoiceContext?): String {
        return super.visitChoice(ctx)
    }

    override fun visitSort_decls(ctx: KeYParser.Sort_declsContext?): String {
        return super.visitSort_decls(ctx)
    }

    override fun visitOne_sort_decl(ctx: KeYParser.One_sort_declContext): String =
            buildString {
                if (null != ctx.GENERIC()) {
                    append(ctx.GENERIC().text).append(" ")
                }

                if (null != ctx.PROXY()) {
                    append(ctx.PROXY().text).append(" ")
                }

                if (null != ctx.ABSTRACT()) {
                    append(ctx.ABSTRACT().text).append(" ")
                }

                ctx.sortIds.simple_ident_dots().joinTo(this, ", ") {
                    it.text
                }

                if (null != ctx.ONEOF()) {
                    append(" ")
                    append(ctx.ONEOF().text)
                    append(" ")
                    ctx.oneof_sorts().sortId().joinTo(this, ", ", "{", "}") {
                        append(ref<Symbol.SORT>(it.text))
                    }
                }
                if (null != ctx.EXTENDS()) {
                    append(" ")
                    append(ctx.EXTENDS().text).append(" ")
                    ctx.sortExt.sortId().joinTo(this, ", ") {
                        it.accept(this@PrettyPrinter)
                    }
                }
                append(ctx.SEMI().text)
            }


    private inline fun <reified T : Symbol> ref(text: String): String {
        if (!printReferences) return "$text "
        val s = index.find { (a, b) -> b is T && b.displayName == text }?.second
        return if (s != null)
            "<a href=\"${s.href}\">$text</a> "
        else
            "text ".also {
                System.err.println("Could not found symbol for $text : ${T::class.java.simpleName}")
            }
    }

    override fun visitSimple_ident_dots(ctx: KeYParser.Simple_ident_dotsContext?): String {
        return super.visitSimple_ident_dots(ctx)
    }

    override fun visitSimple_ident_dots_comma_list(ctx: KeYParser.Simple_ident_dots_comma_listContext?): String {
        return super.visitSimple_ident_dots_comma_list(ctx)
    }

    override fun visitExtends_sorts(ctx: KeYParser.Extends_sortsContext?): String {
        return super.visitExtends_sorts(ctx)
    }

    override fun visitOneof_sorts(ctx: KeYParser.Oneof_sortsContext?): String {
        return super.visitOneof_sorts(ctx)
    }

    override fun visitKeyjavatype(ctx: KeYParser.KeyjavatypeContext?): String {
        return super.visitKeyjavatype(ctx)
    }

    override fun visitProg_var_decls(ctx: KeYParser.Prog_var_declsContext?): String {
        return super.visitProg_var_decls(ctx)
    }

    override fun visitString_literal(ctx: KeYParser.String_literalContext?): String {
        return super.visitString_literal(ctx)
    }

    override fun visitString_value(ctx: KeYParser.String_valueContext?): String {
        return super.visitString_value(ctx)
    }

    override fun visitSimple_ident(ctx: KeYParser.Simple_identContext?): String {
        return super.visitSimple_ident(ctx)
    }

    override fun visitSimple_ident_comma_list(ctx: KeYParser.Simple_ident_comma_listContext?): String {
        return super.visitSimple_ident_comma_list(ctx)
    }

    override fun visitSchema_var_decls(ctx: KeYParser.Schema_var_declsContext?): String {
        return super.visitSchema_var_decls(ctx)
    }

    override fun visitOne_schema_var_decl(ctx: KeYParser.One_schema_var_declContext?): String {
        return super.visitOne_schema_var_decl(ctx)
    }

    override fun visitSchema_modifiers(ctx: KeYParser.Schema_modifiersContext?): String {
        return super.visitSchema_modifiers(ctx)
    }

    override fun visitOne_schema_modal_op_decl(ctx: KeYParser.One_schema_modal_op_declContext?): String {
        return super.visitOne_schema_modal_op_decl(ctx)
    }

    override fun visitPred_decl(ctx: KeYParser.Pred_declContext?): String {
        return super.visitPred_decl(ctx)
    }

    override fun visitPred_decls(ctx: KeYParser.Pred_declsContext?): String {
        return super.visitPred_decls(ctx)
    }

    override fun visitFunc_decl(ctx: KeYParser.Func_declContext?): String {
        return super.visitFunc_decl(ctx)
    }

    override fun visitFunc_decls(ctx: KeYParser.Func_declsContext?): String {
        return super.visitFunc_decls(ctx)
    }

    override fun visitArg_sorts_or_formula(ctx: KeYParser.Arg_sorts_or_formulaContext?): String {
        return super.visitArg_sorts_or_formula(ctx)
    }

    override fun visitArg_sorts_or_formula_helper(ctx: KeYParser.Arg_sorts_or_formula_helperContext?): String {
        return super.visitArg_sorts_or_formula_helper(ctx)
    }

    override fun visitTransform_decl(ctx: KeYParser.Transform_declContext?): String {
        return super.visitTransform_decl(ctx)
    }

    override fun visitTransform_decls(ctx: KeYParser.Transform_declsContext?): String {
        return super.visitTransform_decls(ctx)
    }

    override fun visitArrayopid(ctx: KeYParser.ArrayopidContext?): String {
        return super.visitArrayopid(ctx)
    }

    override fun visitArg_sorts(ctx: KeYParser.Arg_sortsContext?): String {
        return super.visitArg_sorts(ctx)
    }

    override fun visitWhere_to_bind(ctx: KeYParser.Where_to_bindContext?): String {
        return super.visitWhere_to_bind(ctx)
    }

    override fun visitRuleset_decls(ctx: KeYParser.Ruleset_declsContext?): String {
        return super.visitRuleset_decls(ctx)
    }

    override fun visitSortId(ctx: KeYParser.SortIdContext): String {
        return ref<Symbol.SORT>(ctx.text)
    }

    override fun visitId_declaration(ctx: KeYParser.Id_declarationContext?): String {
        return super.visitId_declaration(ctx)
    }

    override fun visitFuncpred_name(ctx: KeYParser.Funcpred_nameContext?): String {
        return super.visitFuncpred_name(ctx)
    }

    override fun visitTermEOF(ctx: KeYParser.TermEOFContext?): String {
        return super.visitTermEOF(ctx)
    }

    override fun visitBoolean_literal(ctx: KeYParser.Boolean_literalContext?): String {
        return super.visitBoolean_literal(ctx)
    }

    override fun visitLiterals(ctx: KeYParser.LiteralsContext?): String {
        return super.visitLiterals(ctx)
    }

    override fun visitNegation(ctx: KeYParser.NegationContext?): String {
        return super.visitNegation(ctx)
    }

    override fun visitTermIfExThenElse(ctx: KeYParser.TermIfExThenElseContext?): String {
        return super.visitTermIfExThenElse(ctx)
    }

    override fun visitEquivalence_term(ctx: KeYParser.Equivalence_termContext?): String {
        return super.visitEquivalence_term(ctx)
    }

    override fun visitTermSubstitution(ctx: KeYParser.TermSubstitutionContext?): String {
        return super.visitTermSubstitution(ctx)
    }

    override fun visitTermParen(ctx: KeYParser.TermParenContext?): String {
        return super.visitTermParen(ctx)
    }

    override fun visitTermCompare(ctx: KeYParser.TermCompareContext?): String {
        return super.visitTermCompare(ctx)
    }

    override fun visitTermEquals(ctx: KeYParser.TermEqualsContext?): String {
        return super.visitTermEquals(ctx)
    }

    override fun visitBracket_access_indexrange(ctx: KeYParser.Bracket_access_indexrangeContext?): String {
        return super.visitBracket_access_indexrange(ctx)
    }

    override fun visitTermAccess(ctx: KeYParser.TermAccessContext?): String {
        return super.visitTermAccess(ctx)
    }

    override fun visitCast(ctx: KeYParser.CastContext?): String {
        return super.visitCast(ctx)
    }

    override fun visitParallel(ctx: KeYParser.ParallelContext?): String {
        return super.visitParallel(ctx)
    }

    override fun visitBracket_access_star(ctx: KeYParser.Bracket_access_starContext?): String {
        return super.visitBracket_access_star(ctx)
    }

    override fun visitTermQuantifier(ctx: KeYParser.TermQuantifierContext?): String {
        return super.visitTermQuantifier(ctx)
    }

    override fun visitTermAttribute(ctx: KeYParser.TermAttributeContext?): String {
        return super.visitTermAttribute(ctx)
    }

    override fun visitTermModality(ctx: KeYParser.TermModalityContext?): String {
        return super.visitTermModality(ctx)
    }

    override fun visitTermLocset(ctx: KeYParser.TermLocsetContext?): String {
        return super.visitTermLocset(ctx)
    }

    override fun visitDisjunction_term(ctx: KeYParser.Disjunction_termContext?): String {
        return super.visitDisjunction_term(ctx)
    }

    override fun visitTermNotEquals(ctx: KeYParser.TermNotEqualsContext?): String {
        return super.visitTermNotEquals(ctx)
    }

    override fun visitTermDivisionModulo(ctx: KeYParser.TermDivisionModuloContext?): String {
        return super.visitTermDivisionModulo(ctx)
    }

    override fun visitElementary_update_term(ctx: KeYParser.Elementary_update_termContext?): String {
        return super.visitElementary_update_term(ctx)
    }

    override fun visitBracket_access_heap_term(ctx: KeYParser.Bracket_access_heap_termContext?): String {
        return super.visitBracket_access_heap_term(ctx)
    }

    override fun visitTermIfThenElse(ctx: KeYParser.TermIfThenElseContext?): String {
        return super.visitTermIfThenElse(ctx)
    }

    override fun visitAbbreviation(ctx: KeYParser.AbbreviationContext?): String {
        return super.visitAbbreviation(ctx)
    }

    override fun visitTermUpdate(ctx: KeYParser.TermUpdateContext?): String {
        return super.visitTermUpdate(ctx)
    }

    override fun visitTermCall(ctx: KeYParser.TermCallContext?): String {
        return super.visitTermCall(ctx)
    }

    override fun visitTermWeakArith(ctx: KeYParser.TermWeakArithContext?): String {
        return super.visitTermWeakArith(ctx)
    }

    override fun visitDotAll(ctx: KeYParser.DotAllContext?): String {
        return super.visitDotAll(ctx)
    }

    override fun visitTermLabeled(ctx: KeYParser.TermLabeledContext?): String {
        return super.visitTermLabeled(ctx)
    }

    override fun visitTermHeap(ctx: KeYParser.TermHeapContext?): String {
        return super.visitTermHeap(ctx)
    }

    override fun visitBracket_access_heap_upate(ctx: KeYParser.Bracket_access_heap_upateContext?): String {
        return super.visitBracket_access_heap_upate(ctx)
    }

    override fun visitTermMult(ctx: KeYParser.TermMultContext?): String {
        return super.visitTermMult(ctx)
    }

    override fun visitUnaryMinus(ctx: KeYParser.UnaryMinusContext?): String {
        return super.visitUnaryMinus(ctx)
    }

    override fun visitImplication_term(ctx: KeYParser.Implication_termContext?): String {
        return super.visitImplication_term(ctx)
    }

    override fun visitConjunction_term(ctx: KeYParser.Conjunction_termContext?): String {
        return super.visitConjunction_term(ctx)
    }

    override fun visitTermLocation(ctx: KeYParser.TermLocationContext?): String {
        return super.visitTermLocation(ctx)
    }

    override fun visitTermLiterals(ctx: KeYParser.TermLiteralsContext?): String {
        return super.visitTermLiterals(ctx)
    }

    override fun visitAccessterm(ctx: KeYParser.AccesstermContext?): String {
        return super.visitAccessterm(ctx)
    }

    override fun visitLabel(ctx: KeYParser.LabelContext?): String {
        return super.visitLabel(ctx)
    }

    override fun visitSingle_label(ctx: KeYParser.Single_labelContext?): String {
        return super.visitSingle_label(ctx)
    }

    override fun visitLocation_term(ctx: KeYParser.Location_termContext?): String {
        return super.visitLocation_term(ctx)
    }

    override fun visitSubstitutionterm(ctx: KeYParser.SubstitutiontermContext?): String {
        return super.visitSubstitutionterm(ctx)
    }

    override fun visitUpdateterm(ctx: KeYParser.UpdatetermContext?): String {
        return super.visitUpdateterm(ctx)
    }

    override fun visitStaticAttributeOrQueryReference(ctx: KeYParser.StaticAttributeOrQueryReferenceContext?): String {
        return super.visitStaticAttributeOrQueryReference(ctx)
    }

    override fun visitAttrid(ctx: KeYParser.AttridContext?): String {
        return super.visitAttrid(ctx)
    }

    override fun visitIfThenElseTerm(ctx: KeYParser.IfThenElseTermContext?): String {
        return super.visitIfThenElseTerm(ctx)
    }

    override fun visitIfExThenElseTerm(ctx: KeYParser.IfExThenElseTermContext?): String {
        return super.visitIfExThenElseTerm(ctx)
    }

    override fun visitQuantifierterm(ctx: KeYParser.QuantifiertermContext?): String {
        return super.visitQuantifierterm(ctx)
    }

    override fun visitLocset_term(ctx: KeYParser.Locset_termContext?): String {
        return super.visitLocset_term(ctx)
    }

    override fun visitBound_variables(ctx: KeYParser.Bound_variablesContext?): String {
        return super.visitBound_variables(ctx)
    }

    override fun visitOne_bound_variable(ctx: KeYParser.One_bound_variableContext?): String {
        return super.visitOne_bound_variable(ctx)
    }

    override fun visitArgument_list(ctx: KeYParser.Argument_listContext?): String {
        return super.visitArgument_list(ctx)
    }

    override fun visitNumber(ctx: KeYParser.NumberContext?): String {
        return super.visitNumber(ctx)
    }

    override fun visitChar_literal(ctx: KeYParser.Char_literalContext?): String {
        return super.visitChar_literal(ctx)
    }

    override fun visitVarId(ctx: KeYParser.VarIdContext?): String {
        return super.visitVarId(ctx)
    }

    override fun visitVarIds(ctx: KeYParser.VarIdsContext?): String {
        return super.visitVarIds(ctx)
    }

    override fun visitTriggers(ctx: KeYParser.TriggersContext?): String {
        return super.visitTriggers(ctx)
    }

    override fun visitTaclet(ctx: KeYParser.TacletContext?): String {
        return super.visitTaclet(ctx)
    }

    override fun visitModifiers(ctx: KeYParser.ModifiersContext?): String {
        return super.visitModifiers(ctx)
    }

    override fun visitSeq(ctx: KeYParser.SeqContext?): String {
        return super.visitSeq(ctx)
    }

    override fun visitSeqEOF(ctx: KeYParser.SeqEOFContext?): String {
        return super.visitSeqEOF(ctx)
    }

    override fun visitTermorseq(ctx: KeYParser.TermorseqContext?): String {
        return super.visitTermorseq(ctx)
    }

    override fun visitSemisequent(ctx: KeYParser.SemisequentContext?): String {
        return super.visitSemisequent(ctx)
    }

    override fun visitVarexplist(ctx: KeYParser.VarexplistContext?): String {
        return super.visitVarexplist(ctx)
    }

    override fun visitVarexpId(ctx: KeYParser.VarexpIdContext?): String {
        return super.visitVarexpId(ctx)
    }

    override fun visitVarexp_argument(ctx: KeYParser.Varexp_argumentContext?): String {
        return super.visitVarexp_argument(ctx)
    }

    override fun visitVarexp(ctx: KeYParser.VarexpContext?): String {
        return super.visitVarexp(ctx)
    }

    override fun visitGoalspecs(ctx: KeYParser.GoalspecsContext?): String {
        return super.visitGoalspecs(ctx)
    }

    override fun visitGoalspecwithoption(ctx: KeYParser.GoalspecwithoptionContext?): String {
        return super.visitGoalspecwithoption(ctx)
    }

    override fun visitOption(ctx: KeYParser.OptionContext?): String {
        return super.visitOption(ctx)
    }

    override fun visitOption_list(ctx: KeYParser.Option_listContext?): String {
        return super.visitOption_list(ctx)
    }

    override fun visitGoalspec(ctx: KeYParser.GoalspecContext?): String {
        return super.visitGoalspec(ctx)
    }

    override fun visitReplacewith(ctx: KeYParser.ReplacewithContext?): String {
        return super.visitReplacewith(ctx)
    }

    override fun visitAdd(ctx: KeYParser.AddContext?): String {
        return super.visitAdd(ctx)
    }

    override fun visitAddrules(ctx: KeYParser.AddrulesContext?): String {
        return super.visitAddrules(ctx)
    }

    override fun visitAddprogvar(ctx: KeYParser.AddprogvarContext?): String {
        return super.visitAddprogvar(ctx)
    }

    override fun visitTacletlist(ctx: KeYParser.TacletlistContext?): String {
        return super.visitTacletlist(ctx)
    }

    override fun visitPvset(ctx: KeYParser.PvsetContext?): String {
        return super.visitPvset(ctx)
    }

    override fun visitRulesets(ctx: KeYParser.RulesetsContext?): String {
        return super.visitRulesets(ctx)
    }

    override fun visitRuleset(ctx: KeYParser.RulesetContext?): String {
        return super.visitRuleset(ctx)
    }

    override fun visitMetaId(ctx: KeYParser.MetaIdContext?): String {
        return super.visitMetaId(ctx)
    }

    override fun visitMetaTerm(ctx: KeYParser.MetaTermContext?): String {
        return super.visitMetaTerm(ctx)
    }

    override fun visitContracts(ctx: KeYParser.ContractsContext?): String {
        return super.visitContracts(ctx)
    }

    override fun visitInvariants(ctx: KeYParser.InvariantsContext?): String {
        return super.visitInvariants(ctx)
    }

    override fun visitOne_contract(ctx: KeYParser.One_contractContext?): String {
        return super.visitOne_contract(ctx)
    }

    override fun visitOne_invariant(ctx: KeYParser.One_invariantContext?): String {
        return super.visitOne_invariant(ctx)
    }

    override fun visitRulesOrAxioms(ctx: KeYParser.RulesOrAxiomsContext?): String {
        return super.visitRulesOrAxioms(ctx)
    }

    override fun visitBootClassPath(ctx: KeYParser.BootClassPathContext?): String {
        return super.visitBootClassPath(ctx)
    }

    override fun visitClassPaths(ctx: KeYParser.ClassPathsContext?): String {
        return super.visitClassPaths(ctx)
    }

    override fun visitJavaSource(ctx: KeYParser.JavaSourceContext?): String {
        return super.visitJavaSource(ctx)
    }

    override fun visitOneJavaSource(ctx: KeYParser.OneJavaSourceContext?): String {
        return super.visitOneJavaSource(ctx)
    }

    override fun visitProfile(ctx: KeYParser.ProfileContext?): String {
        return super.visitProfile(ctx)
    }

    override fun visitPreferences(ctx: KeYParser.PreferencesContext?): String {
        return super.visitPreferences(ctx)
    }

    override fun visitProofScript(ctx: KeYParser.ProofScriptContext?): String {
        return super.visitProofScript(ctx)
    }

    override fun visitProof(ctx: KeYParser.ProofContext?): String {
        return super.visitProof(ctx)
    }
}