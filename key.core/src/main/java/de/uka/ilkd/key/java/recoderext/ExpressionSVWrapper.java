/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.JOperatorSV;

import recoder.java.LoopInitializer;
import recoder.java.SourceVisitor;
import recoder.java.StatementContainer;
import recoder.java.expression.Literal;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.ReferenceSuffix;

public class ExpressionSVWrapper extends Literal
        implements LoopInitializer, KeYRecoderExtension, SVWrapper, ReferencePrefix {

    /**
     *
     */
    private static final long serialVersionUID = 7659491655661716390L;
    protected final JOperatorSV sv;
    protected ReferenceSuffix suff;


    protected StatementContainer statementParent = null;

    protected ExpressionSVWrapper(ExpressionSVWrapper proto) {
        super(proto);
        sv = proto.getSV();
        expressionParent = null;
    }

    public ExpressionSVWrapper(JOperatorSV sv) {
        this.sv = sv;
        expressionParent = null;
    }

    /**
     * Make parent role valid.
     */
    public void makeParentRoleValid() {
    }


    @Override
    public JOperatorSV getSV() {
        return sv;
    }


    // don't think we need it
    @Override
    public void accept(SourceVisitor v) {
    }

    @Override
    public ExpressionSVWrapper deepClone() {
        return new ExpressionSVWrapper(sv);
    }

    /**
     * Get statement container.
     *
     * @return the statement container.
     */
    @Override
    public StatementContainer getStatementContainer() {
        return statementParent;
    }

    /**
     * Set statement container.
     *
     * @param c a statement container.
     */
    @Override
    public void setStatementContainer(StatementContainer c) {
        statementParent = c;
    }


    @Override
    public ReferenceSuffix getReferenceSuffix() {
        return suff;
    }

    /**
     * Set reference suffix.
     *
     * @param path a reference suffix.
     */
    @Override
    public void setReferenceSuffix(ReferenceSuffix path) {
        suff = path;
    }


    @Override
    public Object getEquivalentJavaType() {
        throw new Error("mulbrich: what to do here?!");
    }
}
