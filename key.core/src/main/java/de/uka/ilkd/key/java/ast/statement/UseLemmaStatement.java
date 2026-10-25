/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.speclang.njml.JmlParser;

/**
 * JML use_lemma statement
 *
 * @author Mattias Ulbrich
 */
public class UseLemmaStatement extends JavaStatement {

    /**
     * The parser context of the statement produced during parsing.
     */
    private final JmlParser.PostfixexprContext context;

    /** Constructor used in recoderext */
    public UseLemmaStatement(JmlParser.PostfixexprContext context, PositionInfo positionInfo) {
        super(positionInfo);
        this.context = context;
    }

    /** Constructor used when cloning */
    public UseLemmaStatement(UseLemmaStatement copyFrom) {
        this(copyFrom.context, copyFrom.getPositionInfo());
    }

    /**
     * Removes the attached parser context from this set statement
     *
     * @return the parser context that was attached
     */
    public JmlParser.PostfixexprContext getParserContext() {
        return context;
    }

    /** {@inheritDoc} */
    @Override
    public void visit(Visitor v) {
        v.performActionOnUseLemmaStatement(this);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        throw new IndexOutOfBoundsException("UseLemmaStatement has no program children");
    }

    @Override
    protected int computeHashCode() {
        return System.identityHashCode(this);
    }
}
