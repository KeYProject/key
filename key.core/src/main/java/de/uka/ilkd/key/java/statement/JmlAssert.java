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

    /**
     * the condition in parse tree form
     */
    private KeyAst.Expression condition;

    /**
     * @param kind assert or assume
     * @param condition the condition of this statement
     * @param positionInfo the position information for this statement
     */
    public JmlAssert(TextualJMLAssertStatement.Kind kind, KeyAst.Expression condition,
            PositionInfo positionInfo) {
        super(positionInfo);
        this.kind = kind;
        this.condition = condition;
    }

    /**
     * @param children the children of this element
     */
    public JmlAssert(ExtList children) {
        super(children);
        this.kind = Objects.requireNonNull(children.get(TextualJMLAssertStatement.Kind.class));
        this.condition = Objects.requireNonNull(children.get(KeyAst.Expression.class));
    }

    public JmlAssert(JmlAssert other) {
        this(other.kind, other.condition, other.getPositionInfo());
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
}
