/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.speclang.njml.JmlParser;



/**
 * JML set statement
 *
 * @author Julian Wiesler
 */
public class SetStatement extends JavaStatement {

    /**
     * The target of the assignment as a term. Either a heap access for a ghost field
     * or a ghost variable.
     */
    public static int INDEX_TARGET = 0;

    /**
     * The value of the assignment as a term.
     */
    public static int INDEX_VALUE = 1;

    /**
     * The parser context of the statement produced during parsing.
     */
    private final JmlParser.Set_statementContext context;

    /** Constructor used in recoderext */
    public SetStatement(JmlParser.Set_statementContext context, PositionInfo positionInfo) {
        super(positionInfo);
        this.context = context;
    }

    /** Constructor used when cloning */
    public SetStatement(SetStatement copyFrom) {
        this(copyFrom.context, copyFrom.getPositionInfo());
    }

    /**
     * Removes the attached parser context from this set statement
     *
     * @deprecated weigl: The use of {@link org.antlr.v4.runtime.ParserRuleContext} directly is
     *             discouraged. It adds
     *             an (often) unnecessary dependency to the ANTLR across the project.
     * @return the parser context that was attached
     */
    @Deprecated
    public JmlParser.Set_statementContext getParserContext() {
        return context;
    }


    /** {@inheritDoc} */
    @Override
    public void visit(Visitor v) {
        v.performActionOnSetStatement(this);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        throw new IndexOutOfBoundsException("SetStatement has no program children");
    }
}
