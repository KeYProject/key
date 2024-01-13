/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.TermReplacementMap;
import de.uka.ilkd.key.speclang.njml.JmlParser;

import org.key_project.util.ExtList;

/**
 * JML set statement
 *
 * @author Julian Wiesler
 */
public class SetStatement extends JavaStatement {
    /**
     * The parser context of the statement produced during parsing.
     */
    private final JmlParser.Set_statementContext context;

    /**
     * The target of the assignment as a term. Either a heap access for a ghost field
     * or a ghost variable.
     */
    private Term target;

    /**
     * The value of the assignment as a term.
     */
    private Term value;

    /** Constructor used in recoderext */
    public SetStatement(ExtList children, JmlParser.Set_statementContext context) {
        super(children);
        this.context = context;
    }

    /** Constructor used when cloning */
    public SetStatement(ExtList children) {
        this(children, null);
    }

    /**
     * Removes the attached parser context from this set statement
     *
     * @return the parser context that was attached
     */
    public JmlParser.Set_statementContext getParserContext() {
        return context;
    }

    public void setTranslated(Term target, Term value) {
        this.target = target;
        this.value = value;
    }

    public Term getTarget() {
        return target;
    }

    public Term getValue() {
        return value;
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

    @Override
    public String toString() {
        return super.toString();
    }
}
