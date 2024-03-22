/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.translation.Context;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.mergerule.MergeParamsSpec;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.antlr.v4.runtime.ParserRuleContext;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Stateful service for translating JML into KeY entities.
 * <p>
 * This facade stores the parsing context of JML constructs, e.g., the return or self variable, the
 * parameters. You can set these values via the builder methods. The {@code translate*} methods
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
    private SpecMathMode specMathMode;
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
     * Generate an empty jml i/o instance.
     *
     * @param services a service object used for constructing the terms
     */
    public JmlIO(Services services) {
        this.services = services;
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
    public JmlIO(@NonNull Services services, @Nullable KeYJavaType specInClass,
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
    public ObservableClauseData translateRepresents(ParserRuleContext clause) {
        Object interpret = interpret(clause);
        return (ObservableClauseData) interpret;
    }

    /**
     * Interpret a given represents clause.
     * <p>
     * Note weigl: This method does not add the given term label to the returned objects. I am not
     * if this is currently wanted/needed.
     *
     * @throws ClassCastException if unsuitable parser rule context is given@param clause
     */
    public @NonNull ObservableClauseData translateRepresents(
            @NonNull LabeledParserRuleContext clause) {
        return translateRepresents(clause.first);
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
        return services.getTermBuilder().addLabel(term, new OriginTermLabel.Origin(type));
    }


    /**
     * Interpret a labeled term (breaks clauses, continue clauses).
     */
    public LabeledClause translateLabeledClause(LabeledParserRuleContext parserRuleContext,
            OriginTermLabel.SpecType type) {
        var labeledClause = (LabeledClause) interpret(parserRuleContext.first);
        return new LabeledClause(labeledClause.label(),
            attachTermLabel(labeledClause.term(), type));
    }


    /**
     * Interpret a merge params.
     */
    public MergeParamsSpec translateMergeParams(JmlParser.MergeparamsspecContext ctx) {
        return (MergeParamsSpec) interpret(ctx);
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
        Translator visitor = new Translator(services, specInClass, selfVar, specMathMode, paramVars,
            resultVar, excVar, atPres, atBefores);
        Object obj = ctx.accept(visitor);
        ImmutableList<PositionedString> newWarnings = ImmutableList.fromList(visitor.getWarnings());
        warnings = warnings.prepend(newWarnings);
        return obj;
    }

    /**
     * Interpret the given parse tree as an JML expression in the current context.
     */
    public @NonNull Term translateTerm(@NonNull ParserRuleContext expr) {
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
        if (expr.second != null) {
            return services.getTermBuilder().addLabel(term, expr.second);
        } else {
            return term;
        }
    }

    /**
     * Interpret the given parse tree as an JML expression in the current context. Attach both given
     * labels {@code type} and in labeled parse tree.
     */
    public Term translateTerm(LabeledParserRuleContext expr, OriginTermLabel.SpecType type) {
        Term term = translateTerm(expr.first);
        OriginTermLabel.Origin origin = new OriginTermLabel.Origin(type);
        if (expr.second != null) {
            return services.getTermBuilder().addLabel(term, expr.second);
        } else {
            return services.getTermBuilder().addLabel(term, origin);
        }
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
    public @NonNull InfFlowSpec translateInfFlow(@NonNull ParserRuleContext expr) {
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
    public DependencyContractData translateDependencyContract(
            ParserRuleContext ctx) {
        return (DependencyContractData) interpret(ctx);
    }

    /**
     * Translates a dependency contract.
     * <p>
     * Note (weigl): No label is currently attached.
     *
     * @throws ClassCastException if the {@code ctx} is not suitable
     */
    public DependencyContractData translateDependencyContract(
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
     * Sets the spec math mode.
     */
    public JmlIO specMathMode(@NonNull SpecMathMode specMathMode) {
        this.specMathMode = specMathMode;
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
     * Sets class type, spec math mode and self var.
     */
    public JmlIO context(Context context) {
        this.classType(context.classType());
        this.specMathMode(context.specMathMode());
        this.selfVar(context.selfVar());
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
        this.specMathMode = null;
        clearWarnings();
        exceptionVariable(null);
        parameters(ImmutableSLList.nil());
        return this;
    }

    // endregion

    /**
     * returns the gathered interpretation warnings, e.g., deprecated constructs.
     */
    public ImmutableList<PositionedString> getWarnings() {
        return warnings;
    }

    public void clearWarnings() {
        warnings = ImmutableSLList.nil();
    }

    // region
    // endregion
}
