/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import java.util.Objects;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLAssertStatement;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableList;

import org.antlr.v4.runtime.ParserRuleContext;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * A JML assert statement.
 *
 * @author Benjamin Takacs
 */
public class JmlAssert extends JavaStatement {
    /**
     * Index in the list of terms of
     * {@link de.uka.ilkd.key.proof.mgt.SpecificationRepository.JmlStatementSpec}
     */
    public static final int INDEX_CONDITION = 0;
    /**
     * the kind of the statement, assert or assume
     */
    private final TextualJMLAssertStatement.Kind kind;

    /*
     * Temporary solution until full jml labels are there ...
     * (To be clarified if compatible still)
     */
    private final String optLabel;

    /**
     * the condition in parse tree form
     */
    private final KeyAst.Expression condition;

    /**
     * the assertion proof in parse tree form
     */
    private final KeyAst.@Nullable JMLProofScript assertionProof;

    /**
     * @param kind assert or assume
     * @param condition the condition of this statement
     * @param assertionProof the optional proof for an assert statement (not for assume)
     * @param positionInfo the position information for this statement
     */
    public JmlAssert(TextualJMLAssertStatement.Kind kind, String label, KeyAst.Expression condition,
            KeyAst.@Nullable JMLProofScript assertionProof,
            PositionInfo positionInfo) {
        super(positionInfo);
        this.kind = kind;
        this.optLabel = label;
        this.condition = condition;
        this.assertionProof = assertionProof;
    }

    /**
     * @param children the children of this element
     */
    public JmlAssert(ExtList children) {
        super(children);
        this.kind = Objects.requireNonNull(children.get(TextualJMLAssertStatement.Kind.class));
        this.optLabel = children.get(String.class);
        this.condition = Objects.requireNonNull(children.get(KeyAst.Expression.class));
        // script may be null
        this.assertionProof = children.get(KeyAst.JMLProofScript.class);
    }

    public JmlAssert(JmlAssert other) {
        this(other.kind, other.optLabel, other.condition, other.assertionProof, other.getPositionInfo());
    }

    public TextualJMLAssertStatement.Kind getKind() {
        return kind;
    }

    /*
     * @return the condition in String form
     * public String getConditionText() {
     * if (cond != null) {
     * return LogicPrinter.quickPrintTerm(cond, services);
     * }
     * // this will lose whitespace, so e.g. \forall will not be printed correctly
     * // but normally the term form should get printed.
     * return condition.first.getText().substring(kind.name().length());
     * }
     */

    /** Returns the condition as an encapsulated {@link org.antlr.v4.runtime.ParserRuleContext} */
    public KeyAst.Expression getCondition() {
        return condition;
    }

    /*
     * Returns the condition in Term form.
     *
     * You have to call translateCondition(JmlIO) before getting useful values.
     *
     * @return the condition in Term form if it was already translated else null
     *
     * @param self the Term for {@code this} in the current context
     *
     * @param services services
     * public Term getCond(final Term self, final Services services) {
     * final TermFactory termFactory = services.getTermFactory();
     * final TermReplacementMap replacementMap = new TermReplacementMap(termFactory);
     * if (self != null) {
     * replacementMap.replaceSelf(vars.selfVar, self, services);
     * }
     * replacementMap.replaceRemembranceLocalVariables(vars.atPreVars, vars.atPres, services);
     * replacementMap.replaceRemembranceLocalVariables(vars.atBeforeVars, vars.atBefores,
     * services);
     * final OpReplacer replacer =
     * new OpReplacer(replacementMap, termFactory, services.getProof());
     * return replacer.replace(cond);
     * }
     */


    /*
     * Translates the condition of this JML assert statement to a Term.
     *
     * Use as soon as possible, but can only be called once.
     *
     * @param jmlIo the JmlIO to use to translate the condition
     *
     * @param pv the program variables to use for the translation
     *
     * @throws IllegalStateException if this JmlAssert already has a condition in Term form
     * public void translateCondition(final JmlIO jmlIo, final ProgramVariableCollection pv) {
     * if (cond != null) {
     * throw new IllegalStateException("condition can only be set once");
     * }
     * this.vars = pv;
     * jmlIo.selfVar(pv.selfVar).parameters(pv.paramVars).resultVariable(pv.resultVar)
     * .exceptionVariable(pv.excVar).atPres(pv.atPres).atBefore(pv.atBefores);
     * this.cond = jmlIo.translateTermAsFormula(condition);
     * condition = null;
     * }
     */

    @Override
    public boolean equals(final Object o) {
        if (this == o) {
            return true;
        }
        if (!super.equals(o)) {
            return false;
        }
        // super.equals() check classes
        final JmlAssert jmlAssert = (JmlAssert) o;
        return kind == jmlAssert.kind && Objects.equals(condition, jmlAssert.condition);
    }

    // hashCode() caches the result of computeHashCode()
    // so override that instead of hashCode which is final
    @Override
    protected int computeHashCode() {
        return System.identityHashCode(this);
    }

    public KeyAst.@Nullable JMLProofScript getAssertionProof() {
        return assertionProof;
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        throw new IndexOutOfBoundsException("JmlAssert has no program children");
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnJmlAssert(this);
    }

    /**
     * This method collects all terms contained in this assertion. This is at least the condition.
     * If there is a proof script, all terms in the proof script are collected as well.
     *
     * @return a freshly created list of at least one term
     */
    public @NonNull ImmutableList<ParserRuleContext> collectTerms() {
        ImmutableList<ParserRuleContext> result = ImmutableList.of();
        if (assertionProof != null) {
            result = result.prepend(assertionProof.collectTerms());
        }
        result = result.prepend(condition.ctx);
        return result;
    }

    public String getOptLabel() {
        return optLabel;
    }
}
