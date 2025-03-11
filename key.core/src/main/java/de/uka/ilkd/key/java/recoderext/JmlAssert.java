/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLAssertStatement;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLAssertStatement.Kind;
import de.uka.ilkd.key.speclang.njml.JmlParser.AssertionProofContext;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;

import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;
import recoder.java.statement.JavaStatement;

/**
 * A JML assert statement.
 *
 * @author Benjamin Takacs
 */
public class JmlAssert extends JavaStatement {

    /**
     * The kind of this statement either ASSERT or ASSUME
     */
    private final TextualJMLAssertStatement.Kind kind;
    private final AssertionProofContext assertionProof;


    /**
     * The condition of this statement in parse tree form
     */
    // this isn't serializable, but that shouldn't be a problem for KeY
    private final KeyAst.Expression condition;
    private final String optLabel;

    /**
     * @param kind the kind of this statement
     * @param condition the condition for this statement
     * @param optLabel
     */
    public JmlAssert(TextualJMLAssertStatement.Kind kind, KeyAst.Expression condition, String optLabel) {
        this(kind, condition, null, optLabel);
    }

    public JmlAssert(Kind kind,  KeyAst.Expression condition,
                     AssertionProofContext assertionProof, String optLabel) {
        this.kind = kind;
        this.assertionProof = assertionProof;
        this.condition = condition;
        this.optLabel = optLabel;
    }

    /**
     * copy constructor
     *
     * @param proto the original JML assert statement to copy
     */
    public JmlAssert(JmlAssert proto) {
        super(proto);
        this.kind = proto.kind;
        this.condition = proto.condition;
        this.assertionProof = proto.assertionProof;
        this.optLabel = proto.optLabel;
    }

    public TextualJMLAssertStatement.Kind getKind() {
        return kind;
    }

    public KeyAst.Expression getCondition() {
        return condition;
    }

    public AssertionProofContext getAssertionProof() {
        return assertionProof;
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int i) {
        throw new IndexOutOfBoundsException("JmlAssert has no program children");
    }

    @Override
    public int getChildPositionCode(ProgramElement child) {
        return -1;
    }

    @Override
    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        return false;
    }

    @Override
    public void accept(SourceVisitor sourceVisitor) {
        // should be fine to leave blank
    }

    @Override
    public Statement deepClone() {
        return new JmlAssert(this);
    }

    public String getOptLabel() {
        return optLabel;
    }
}
