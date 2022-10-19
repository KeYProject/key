package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.speclang.njml.JmlParser;

import org.key_project.util.ExtList;

/**
 * JML set statement
 *
 * @author Julian Wiesler
 */
public class SetStatement extends CopyAssignment {
    /** The parser context of the statement */
    private JmlParser.Set_statementContext context;

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
    public JmlParser.Set_statementContext takeParserContext() {
        var context = this.context;
        this.context = null;
        return context;
    }

    /** {@inheritDoc} */
    @Override
    public void visit(Visitor v) {
        v.performActionOnSetStatement(this);
    }
}
