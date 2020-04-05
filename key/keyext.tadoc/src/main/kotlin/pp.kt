package org.key_project.core.doc

import de.uka.ilkd.key.nparser.KeYLexer
import de.uka.ilkd.key.nparser.KeYParser
import de.uka.ilkd.key.nparser.KeYParserBaseVisitor
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.Token
import org.antlr.v4.runtime.tree.ParseTree
import org.antlr.v4.runtime.tree.TerminalNode
import org.key_project.core.doc.Symbol.Type.SORT
import java.util.*
import kotlin.collections.HashMap

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/12/20)
 */
class PrettyPrinter(val index: Index,
                    val currentContext: Symbol,
                    val printReferences: Boolean = true,
                    private val usageIndex: UsageIndex = HashMap())
    : KeYParserBaseVisitor<String>() {

    private val vocabulary = KeYLexer(CharStreams.fromString("")).vocabulary
    private val tokenSymbols = index.filterIsInstance<TokenSymbol>()

    override fun aggregateResult(aggregate: String?, nextResult: String?) =
            (aggregate ?: "") + (nextResult ?: "")

    override fun visitTerminal(node: TerminalNode) = visitToken(node.symbol)

    private fun visitToken(t: Token): String {
        if (t.type == KeYLexer.DOC_COMMENT) return ""
        if (t.type == KeYLexer.LPAREN || t.type == KeYLexer.LBRACE || t.type == KeYLexer.LBRACKET)
            return openParenthesis(t)
        if (t.type == KeYLexer.RPAREN || t.type == KeYLexer.RBRACE || t.type == KeYLexer.RBRACKET)
            return closeParenthesis(t)
        if (t.type == KeYLexer.IDENT && t.text[0] == '#') {
            return printSpan(t.text, "schema-variable")
        }
        val s = tokenSymbols.find { it.tokenType == t.type }
        val text = if (s != null && printReferences)
            "<a class=\"token\" href=\"${s.href}\">${t.text}</a> "
        else
            "${t.text} "
        return printSpan(text, vocabulary.getDisplayName(t.type))
    }

    private fun printSpan(text: String, classes: String) = "<span class=\"token $classes\">${text}</span>"

    private val rainbowColors = arrayOf(
            "#458588",
            "#b16286",
            "#cc241d",
            "#d65d0e",
            "#458588",
            "#b16286",
            "#cc241d",
            "#d65d0e",
            "#458588",
            "#b16286",
            "#cc241d",
            "#d65d0e",
            "#458588",
            "#b16286",
            "#cc241d",
            "#d65d0e")

    private val parenthesisIds = LinkedList<Int>()
    private var parenthesisCounter = 0
    private fun openParenthesis(token: Token): String {
        val p = ++parenthesisCounter
        parenthesisIds.push(p)
        val c = rainbowColors[p % rainbowColors.size]
        return "<span style=\"color:$c\" " +
                "class=\"paired-element\" id=\"open-${p}\" mouseover=\"highlight(${p})\">${token.text}</span>"
    }

    private fun closeParenthesis(token: Token): String {
        val pop = parenthesisIds.pop()
        val c = rainbowColors[pop % rainbowColors.size]
        return "<span style=\"color:$c\" class=\"paired-element\" id=\"close-$pop\" mouseover=\"highlight($pop)\">${token.text}</span>"

    }

    override fun defaultResult() = " "

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
                        append(ref(it.text, SORT))
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


    private fun ref(text: String, vararg types: Symbol.Type): String {
        if (!printReferences) return "$text "
        val s = index.find { b -> b.type in types && b.displayName == text }
        return if (s != null) {
            usageIndex.add(s, currentContext)
            "<a href=\"${s.href}\" class=\"symbol ${s.type.name}\">$text</a> "
        } else
            "$text ".also {
                App.errordpln("Could not found symbol for $text : ${types.toList()}")
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
        return ref(ctx.text, SORT)
    }

    override fun visitId_declaration(ctx: KeYParser.Id_declarationContext?): String {
        return super.visitId_declaration(ctx)
    }

    override fun visitFuncpred_name(ctx: KeYParser.Funcpred_nameContext) = buildString {
        ctx.sortId()?.let {
            appendn(it)
            appendn(ctx.DOUBLECOLON())
        }
        append(ref(ctx.simple_ident_dots().text,
                Symbol.Type.PREDICATE, Symbol.Type.TRANSFORMER, Symbol.Type.FUNCTION))
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

    override fun visitTermIfExThenElse(ctx: KeYParser.TermIfExThenElseContext?): String {
        return super.visitTermIfExThenElse(ctx)
    }

    override fun visitEquivalence_term(ctx: KeYParser.Equivalence_termContext?): String {
        return super.visitEquivalence_term(ctx)
    }

    override fun visitTermParen(ctx: KeYParser.TermParenContext?): String {
        return super.visitTermParen(ctx)
    }


    override fun visitBracket_access_indexrange(ctx: KeYParser.Bracket_access_indexrangeContext?): String {
        return super.visitBracket_access_indexrange(ctx)
    }

    override fun visitTermAccess(ctx: KeYParser.TermAccessContext?): String {
        return super.visitTermAccess(ctx)
    }

    override fun visitTermLocset(ctx: KeYParser.TermLocsetContext?): String {
        return super.visitTermLocset(ctx)
    }

    override fun visitDisjunction_term(ctx: KeYParser.Disjunction_termContext?): String {
        return super.visitDisjunction_term(ctx)
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

    private fun accept(ctx: ParseTree) = ctx.accept(this)
    private fun accept(ctx: Token) = visitToken(ctx)
    private fun StringBuilder.appendn(ctx: ParseTree?) = if (ctx != null) append(accept(ctx)) else this
    private fun StringBuilder.appendn(ctx: Token?) = if (ctx != null) append(accept(ctx)) else this
    private fun StringBuilder.appendn(ctx: ParseTree?, suffix: String): StringBuilder {
        if (ctx != null) appendn(ctx).append(suffix)
        return this
    }

    override fun visitTaclet(ctx: KeYParser.TacletContext) = buildString {
        appendn(ctx.LEMMA(), " ")
        appendn(ctx.name)

        if (ctx.choices_ != null) {
            append(accept(ctx.choices_))
        }
        append(" {\n")


        appendn(ctx.form)


        if (ctx.SCHEMAVAR().isNotEmpty()) {
            for (i in 0 until ctx.SCHEMAVAR().size) {
                appendn(ctx.SCHEMAVAR(i))
                        .append(" ")
                        .appendn(ctx.one_schema_var_decl(i))
                        .append(";\n")
            }
        }

        ctx.ifSeq?.let {
            append(accept(ctx.ASSUMES()))
            append("(")
            append(accept(it))
            append(")\n")
        }

        ctx.find?.let {
            append(accept(ctx.FIND()))
            append("(")
            append(accept(ctx.find))
            append(")\n")
        }

        if (ctx.SAMEUPDATELEVEL().isNotEmpty())
            appendn(ctx.SAMEUPDATELEVEL().first(), "\n")
        if (ctx.INSEQUENTSTATE().isNotEmpty())
            appendn(ctx.INSEQUENTSTATE().first(), "\n")
        if (ctx.ANTECEDENTPOLARITY().isNotEmpty())
            appendn(ctx.ANTECEDENTPOLARITY().first(), "\n")
        if (ctx.INSEQUENTSTATE().isNotEmpty())
            appendn(ctx.INSEQUENTSTATE().first(), "\n")

        if (ctx.VARCOND() != null) {
            appendn(ctx.VARCOND()).append("(").appendn(ctx.varexplist()).append(")\n")
        }
        appendn(ctx.goalspecs())
        appendn(ctx.modifiers())
        append("\n};")
    }


    override fun visitModifiers(ctx: KeYParser.ModifiersContext) = buildString {
        for (i in 0 until ctx.rulesets().size) {
            appendn(ctx.rulesets(0)).append("\n")
        }

        ctx.NONINTERACTIVE().firstOrNull().let {
            appendn(it, "\n")
        }

        ctx.dname?.let {
            appendn(ctx.DISPLAYNAME().first()).append(" ").appendn(ctx.dname).append("\n")
        }

        ctx.htext?.let {
            appendn(ctx.HELPTEXT().first()).append(" ").append(it).append("\n")
        }

        ctx.triggers().forEach { appendn(it) }
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

    override fun visitGoalspecs(ctx: KeYParser.GoalspecsContext) =
            if (ctx.CLOSEGOAL() != null) {
                accept(ctx.CLOSEGOAL())
            } else {
                ctx.goalspecwithoption().joinToString(";\n") { accept(it) }
            } + "\n"

    override fun visitGoalspecwithoption(ctx: KeYParser.GoalspecwithoptionContext) =
            if (ctx.option_list() == null) accept(ctx.goalspec())
            else buildString { appendn(ctx.option_list()).append(" {\n").appendn(ctx.goalspec()).append("}\n") }

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

    override fun visitRulesets(ctx: KeYParser.RulesetsContext) = buildString {
        appendn(ctx.HEURISTICS())
        append(" (")
        ctx.ruleset().joinTo(this, ", ") { accept(it) }
        append(")")
    }

    override fun visitRuleset(ctx: KeYParser.RulesetContext) = ref(ctx.text, Symbol.Type.RULESET)

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