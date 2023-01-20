package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.mergerule.MergeParamsSpec;
import org.antlr.v4.runtime.ParserRuleContext;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Stateful service for translating JML into KeY entities.
 * <p>
 * This facade stores a the parsing context of JML constructs, e.g., the return or self variable,
 * the parameters. You can set these values via the builder methods. The {@code translate*} methods
 * translate a given {@link ParserRuleContext} into a KeY-entity.
 * <p>
 * It also maintains the list of translation warnings, see {@link #getWarnings()}.
 * <p>
 * Internally, this is a type-safe wrapper around the visitor {@link Translator}.
 *
 * @author Alexander Weigl
 * @version 1 (7/1/20)
 * @see Translator
 */
public class JmlIO {
    private ImmutableList<PositionedString> warnings = ImmutableSLList.nil();

    private Services services;
    private KeYJavaType specInClass;
    private ProgramVariable selfVar;
    private ImmutableList<ProgramVariable> paramVars;
    private ProgramVariable resultVar;
    private ProgramVariable excVar;
    private Map<LocationVariable, Term> atPres;
    private Map<LocationVariable, Term> atBefores;

    /**
     * Generate an empty jml i/o instance. No very useful until a {@link #services(Services)} is
     * provided.
     */
    public JmlIO() {
    }

    /**
     * Full constructor of this class. Prefer the use via builder methods.
     *
     * @param services a service object used for constructing the terms
     * @param specInClass the class in which the expression and contracts should be evaluated
     * @param selfVar the self variable considered for {@code this}-references
     * @param paramVars a list of parameter variables
     * @param resultVar the {@code \return}-variable
     * @param excVar the variable to store exception
     * @param atPres i do not know
     * @param atBefores i do not know
     */
    public JmlIO(@Nonnull Services services, @Nullable KeYJavaType specInClass,
            @Nullable ProgramVariable selfVar, @Nullable ImmutableList<ProgramVariable> paramVars,
            @Nullable ProgramVariable resultVar, @Nullable ProgramVariable excVar,
            @Nullable Map<LocationVariable, Term> atPres,
            @Nullable Map<LocationVariable, Term> atBefores) {
        this.services = services;
        this.specInClass = specInClass;
        this.selfVar = selfVar;
        this.paramVars = paramVars;
        this.resultVar = resultVar;
        this.excVar = excVar;
        this.atBefores = atBefores;
        this.atPres = atPres;
    }

    // region translations

    /**
     * Interpret the given parse tree as a represents clause
     *
     * @throws ClassCastException if unsuitable parser rule context is given
     */
    @SuppressWarnings("unchecked")
    public Pair<IObserverFunction, Term> translateRepresents(ParserRuleContext clause) {
        Object interpret = interpret(clause);
        return (Pair<IObserverFunction, Term>) interpret;
    }

    /**
     * Interpret a given represents clause.
     * <p>
     * Note weigl: This method does not add the given term label to the returned objects. I am not
     * if this is currently wanted/needed.
     *
     * @throws ClassCastException if unsuitable parser rule context is given@param clause
     */
    public @Nonnull Pair<IObserverFunction, Term> translateRepresents(
            @Nonnull LabeledParserRuleContext clause) {
        Pair<IObserverFunction, Term> p = translateRepresents(clause.first);
        return new Pair<>(p.first, p.second);
    }

    /**
     * Checks whether the given {@code functionName} is a known JML function for KeY.
     *
     * @param functionName a string
     * @return true if the function is known
     * @see JmlTermFactory#jml2jdl
     */
    public static boolean isKnownFunction(String functionName) {
        return JmlTermFactory.jml2jdl.containsKey(functionName);
    }

    private Term attachTermLabel(Term term, OriginTermLabel.SpecType type) {
        return services.getTermBuilder().addLabel(term,
            new OriginTermLabel(new OriginTermLabel.Origin(type)));
    }


    /**
     * Interpret a labeled term (breaks clauses, continue clauses).
     */
    @SuppressWarnings("unchecked")
    public Pair<Label, Term> translateLabeledClause(LabeledParserRuleContext parserRuleContext,
            OriginTermLabel.SpecType type) {
        Pair<Label, Term> t = (Pair<Label, Term>) interpret(parserRuleContext.first);
        return new Pair<>(t.first, attachTermLabel(t.second, type));
    }


    /**
     * Interpret a merge params.
     */
    public MergeParamsSpec translateMergeParams(JmlParser.MergeparamsspecContext ctx) {
        return (MergeParamsSpec) interpret(ctx);
    }

    /**
     * Parse and interpret class level comments.
     */
    public ImmutableList<TextualJMLConstruct> parseClassLevel(String concatenatedComment,
            String fileName, Position pos) {
        return parseClassLevel(new PositionedString(concatenatedComment, fileName, pos));
    }

    /**
     * Parse and interpret class level comments.
     */
    private ImmutableList<TextualJMLConstruct> parseClassLevel(PositionedString positionedString) {
        JmlLexer lexer = JmlFacade.createLexer(positionedString);
        return parseClassLevel(lexer);
    }

    /**
     * returns the gathered interpretation warnings, e.g., deprecated constructs.
     */
    public ImmutableList<PositionedString> getWarnings() {
        return warnings;
    }

    /**
     * Parse and interpret the given string as a method level construct.
     */
    public ImmutableList<TextualJMLConstruct> parseMethodLevel(String concatenatedComment,
            String fileName, Position position) {
        return parseMethodLevel(new PositionedString(concatenatedComment, fileName, position));
    }

    /**
     * Parse and interpret the given string as an JML expression in the current context.
     */
    public Term parseExpression(PositionedString p) {
        ParserRuleContext ctx = JmlFacade.parseExpr(p);
        SLExpression expr = (SLExpression) interpret(ctx);
        return expr.getTerm();
    }

    /**
     * Interpret the given parse tree as an JML expression in the current context.
     */
    private Object interpret(ParserRuleContext ctx) {
        Translator visitor = new Translator(services, specInClass, selfVar, paramVars, resultVar,
            excVar, atPres, atBefores);
        Object obj = ctx.accept(visitor);
        ImmutableList<PositionedString> newWarnings = ImmutableList.fromList(visitor.getWarnings());
        warnings = warnings.prepend(newWarnings);
        return obj;
    }

    /**
     * Interpret the given parse tree as an JML expression in the current context.
     */
    public @Nonnull Term translateTerm(@Nonnull ParserRuleContext expr) {
        Object interpret = interpret(expr);
        if (interpret instanceof SLExpression) {
            return ((SLExpression) interpret).getTerm();
        } else {
            return (Term) interpret;
        }
    }

    /**
     * Interpret the given parse tree as an JML expression in the current context. Label is
     * attached.
     */
    public Term translateTerm(LabeledParserRuleContext expr) {
        Term term = translateTerm(expr.first);
        if (expr.second != null)
            return services.getTermBuilder().addLabel(term, expr.second);
        else
            return term;
    }

    /**
     * Interpret the given parse tree as an JML expression in the current context. Attach both given
     * labels {@code type} and in labeled parse tree.
     */
    public Term translateTerm(LabeledParserRuleContext expr, OriginTermLabel.SpecType type) {
        Term term = translateTerm(expr.first);
        OriginTermLabel origin = new OriginTermLabel(new OriginTermLabel.Origin(type));
        if (expr.second != null)
            return services.getTermBuilder().addLabel(term, expr.second);
        else
            return services.getTermBuilder().addLabel(term, origin);
    }


    /**
     * Interpret the given parse tree as an JML expression in the current context. Given label is
     * attached.
     */
    public Term translateTerm(ParserRuleContext expr, OriginTermLabel.SpecType type) {
        Term t = translateTerm(expr);
        return attachTermLabel(t, type);
    }

    /**
     * Interpret the given parse tree as a boolean JML expression in the current context. This is
     * for cases where {@link #translateTerm(LabeledParserRuleContext)} would in some cases give a
     * Term of sort formula and in some cases of sort boolean. Label is attached.
     *
     * @param condition a parse tree of a boolean JML expression
     * @return a formula of the given parse tree
     * @see #translateTerm(LabeledParserRuleContext)
     */
    public Term translateTermAsFormula(final LabeledParserRuleContext condition) {
        Term term = services.getTermBuilder().convertToFormula(translateTerm(condition.first));
        if (condition.second != null) {
            return services.getTermBuilder().addLabel(term, condition.second);
        }
        return term;
    }

    /**
     * Parses and interpret the given input as an JML expression in the current context.
     */
    public Term parseExpression(String input) {
        ParserRuleContext ctx = JmlFacade.parseExpr(input);
        SLExpression expr = (SLExpression) interpret(ctx);
        return expr.getTerm();
    }

    /**
     * Translate the given context into an information flow specification.
     *
     * @param expr should be a {@link JmlParser.Separates_clauseContext} or
     *        {@link JmlParser.Determines_clauseContext}, or
     *        {@link JmlParser.Loop_separates_clauseContext} or
     *        {@link JmlParser.Loop_determines_clauseContext}.
     * @return a information flow specification from the given context.
     * @throws ClassCastException if the {@code expr} is not suitable
     */
    public @Nonnull InfFlowSpec translateInfFlow(@Nonnull ParserRuleContext expr) {
        return (InfFlowSpec) this.interpret(expr);
    }

    /**
     * Translate the given context into an information flow specification. Like
     * {@link #translateInfFlow(ParserRuleContext)} but this method can also handles the given
     * label.
     */
    public InfFlowSpec translateInfFlow(LabeledParserRuleContext expr) {
        return translateInfFlow(expr.first);
    }

    /**
     * Translates the given context into a dependency contract, aka, accessible-clause or
     * depends-clause.
     *
     * @param ctx should a {@link JmlParser.Accessible_clauseContext}
     * @return a dependency contract
     * @throws ClassCastException if the {@code ctx} is not suitable
     */
    @SuppressWarnings("unchecked")
    public Triple<IObserverFunction, Term, Term> translateDependencyContract(
            ParserRuleContext ctx) {
        return (Triple<IObserverFunction, Term, Term>) interpret(ctx);
    }

    /**
     * Translates a dependency contract.
     * <p>
     * Note (weigl): No label is currently attached.
     *
     * @throws ClassCastException if the {@code ctx} is not suitable
     */
    public Triple<IObserverFunction, Term, Term> translateDependencyContract(
            LabeledParserRuleContext ctx) {
        return translateDependencyContract(ctx.first);
    }
    // endregion

    // region builder methods

    /**
     * Sets the variable representing the {@code this} reference.
     */
    public JmlIO selfVar(ProgramVariable selfVar) {
        this.selfVar = selfVar;
        return this;
    }

    /**
     * Sets the current list of known parameter. Can also be used to give additionally variables.
     */
    public JmlIO parameters(ImmutableList<ProgramVariable> params) {
        this.paramVars = params;
        return this;
    }

    /**
     * Sets the variable that is used to store exceptions.
     */
    public JmlIO exceptionVariable(ProgramVariable excVar) {
        this.excVar = excVar;
        return this;
    }

    public JmlIO atPres(Map<LocationVariable, Term> atPres) {
        this.atPres = atPres;
        return this;
    }

    /**
     * Sets the variable representing {@code \result}.
     */
    public JmlIO resultVariable(ProgramVariable resultVar) {
        this.resultVar = resultVar;
        return this;
    }

    /**
     * Sets the current services
     */
    public JmlIO services(Services services) {
        this.services = services;
        return this;
    }

    /**
     * Sets the sort/type of the class containing the interpreted JML.
     */
    public JmlIO classType(KeYJavaType classType) {
        this.specInClass = classType;
        return this;
    }

    public JmlIO atBefore(Map<LocationVariable, Term> atBefores) {
        this.atBefores = atBefores;
        return this;
    }

    /**
     * Clears the internal fields.
     */
    public JmlIO clear() {
        resultVariable(null);
        atBefore(null);
        atPres(null);
        classType(null);
        selfVar(null);
        clearWarnings();
        exceptionVariable(null);
        parameters(ImmutableSLList.nil());
        return this;
    }

    public void clearWarnings() {
        warnings = ImmutableSLList.nil();
    }
    // endregion


    // region

    /**
     * Parses a JML constructs on class level, e.g., invariants and methods contracts, and returns a
     * parse tree.
     */
    public ImmutableList<TextualJMLConstruct> parseClassLevel(JmlLexer lexer) {
        @Nonnull
        JmlParser p = JmlFacade.createParser(lexer);
        JmlParser.Classlevel_commentsContext ctx = p.classlevel_comments();
        p.getErrorReporter().throwException();
        jmlCheck(ctx);
        TextualTranslator translator = new TextualTranslator();
        ctx.accept(translator);
        return translator.constructs;
    }

    private void jmlCheck(ParserRuleContext ctx) {
        List<PositionedString> warn = new ArrayList<>();
        for (JmlCheck check : JmlChecks.getJmlChecks()) {
            List<PositionedString> w = check.check(ctx);
            warn.addAll(w);
        }
        this.warnings = warnings.prepend(ImmutableList.fromList(warn));
    }


    /**
     * Parses a JML constructs on class level, e.g., invariants and methods contracts, and returns a
     * parse tree.
     */
    public ImmutableList<TextualJMLConstruct> parseClassLevel(String content) {
        return parseClassLevel(JmlFacade.createLexer(content));
    }

    /**
     * Parses a JML constructs which occurs inside methods (mostly JML statements) and returns a
     * parse tree.
     */
    public ImmutableList<TextualJMLConstruct> parseMethodLevel(PositionedString positionedString) {
        return parseMethodLevel(JmlFacade.createLexer(positionedString));
    }

    /**
     * Parses a JML constructs which occurs inside methods (mostly JML statements) and returns a
     * parse tree.
     */
    private ImmutableList<TextualJMLConstruct> parseMethodLevel(JmlLexer lexer) {
        @Nonnull
        JmlParser p = JmlFacade.createParser(lexer);
        JmlParser.Methodlevel_commentContext ctx = p.methodlevel_comment();
        p.getErrorReporter().throwException();
        jmlCheck(ctx);
        TextualTranslator translator = new TextualTranslator();
        ctx.accept(translator);
        return translator.constructs;
    }
    // endregion
}
