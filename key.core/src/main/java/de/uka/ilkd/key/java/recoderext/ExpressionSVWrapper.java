/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.SchemaVariable;

import recoder.java.Expression;
import recoder.java.ExpressionContainer;
import recoder.java.LoopInitializer;
import recoder.java.NonTerminalProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.StatementContainer;
import recoder.java.expression.Literal;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.ReferenceSuffix;

public class ExpressionSVWrapper extends Literal
        implements Expression, LoopInitializer, KeYRecoderExtension, SVWrapper, ReferencePrefix {

    /**
     *
     */
    private static final long serialVersionUID = 7659491655661716390L;
    protected SchemaVariable sv;
    protected ReferenceSuffix suff;


    protected StatementContainer statementParent = null;

    protected ExpressionSVWrapper(ExpressionSVWrapper proto) {
        super(proto);
        expressionParent = null;
    }

    public ExpressionSVWrapper() {
        expressionParent = null;
    }

    public ExpressionSVWrapper(SchemaVariable sv) {
        this.sv = sv;
        expressionParent = null;
    }

    /**
     * Make parent role valid.
     */
    public void makeParentRoleValid() {
    }

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */
    public NonTerminalProgramElement getASTParent() {
        return expressionParent;
    }


    /**
     * sets the schema variable of sort statement
     *
     * @param sv the SchemaVariable
     */
    public void setSV(SchemaVariable sv) {
        this.sv = sv;
    }


    public SchemaVariable getSV() {
        return sv;
    }


    /**
     * Get expression container.
     *
     * @return the expression container.
     */
    public ExpressionContainer getExpressionContainer() {
        return expressionParent;
    }

    /**
     * Set expression container.
     *
     * @param c an expression container.
     */
    public void setExpressionContainer(ExpressionContainer c) {
        expressionParent = c;
    }

    // don't think we need it
    public void accept(SourceVisitor v) {
    }

    public ExpressionSVWrapper deepClone() {
        return new ExpressionSVWrapper(sv);
    }

    /**
     * Get statement container.
     *
     * @return the statement container.
     */
    public StatementContainer getStatementContainer() {
        return statementParent;
    }

    /**
     * Set statement container.
     *
     * @param c a statement container.
     */
    public void setStatementContainer(StatementContainer c) {
        statementParent = c;
    }


    public ReferenceSuffix getReferenceSuffix() {
        return suff;
    }

    /**
     * Set reference suffix.
     *
     * @param path a reference suffix.
     */
    public void setReferenceSuffix(ReferenceSuffix path) {
        suff = path;
    }


    @Override
    public Object getEquivalentJavaType() {
        throw new Error("mulbrich: what to do here?!");
    }
}
