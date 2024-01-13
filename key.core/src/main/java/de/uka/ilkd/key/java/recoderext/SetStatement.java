/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.speclang.njml.JmlParser;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.statement.JavaStatement;

/**
 * Wrapper for JML set statements which lifts the contained parse tree to the Translator.
 *
 * @author Julian Wiesler
 */
public class SetStatement extends JavaStatement {
    /**
     * Parser context of the assignment
     */
    private final JmlParser.Set_statementContext context;

    /**
     * Primary constructor
     *
     * @param context the context of the assignment
     */
    public SetStatement(JmlParser.Set_statementContext context) {
        this.context = context;
    }

    /**
     * copy constructor
     *
     * @param proto the orginal JML set statement to copy
     */
    public SetStatement(SetStatement proto) {
        super(proto);
        this.context = proto.context;
    }
    /**
     * {@inheritDoc}
     */
    @Override
    public SetStatement deepClone() {
        return new SetStatement(this);
    }

    /**
     * Gets the contained parser context
     *
     * @return the parser context
     */
    public JmlParser.Set_statementContext getParserContext() {
        return context;
    }

    /**
     * A set statement has no recorder AST children
     * @return
     */
    @Override
    public int getChildCount() {
        return 0;
    }

    /**
     * {@inheritDoc}
     *
     * There are no recorder AST children.
     *
     * @throws IndexOutOfBoundsException always
     */
    @Override
    public ProgramElement getChildAt(int index) {
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
    public void accept(SourceVisitor v) {
        // should be fine to leave blank
    }
}
