//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.unittest;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.LoopInitializer;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.java.expression.operator.PostIncrement;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ArrayOp;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.NonRigidFunctionLocation;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;

/**
 * This class represents a NonRigidFunctionLocation beeing an array
 * 
 * @author mbender
 * 
 */
public class ArrayTermRep extends AbstractTermRepresentation {

    private ProgramVariable pvRead;
    private ProgramVariable pvWrite;

    /**
     * @param up
     * @param serv
     * @param tce
     * @param trh
     */
    public ArrayTermRep(AssignmentPair up, Services serv,
            TestCodeExtractor tce, TermRepHandler trh) {
        super(up, serv, tce, trh);
    }

    /**
     * This methods creates a new Array Term for a given AccessOperator and a
     * given 'index-variable'
     * 
     * @param term
     *            denotes the arrayAccessOperator
     * @param pv
     *            the index of the array
     * @return The Array Term that is the ne representation of the NRFL for an
     *         Array
     */
    private Term createArrayAcc(Term term, ProgramVariable pv) {
        final Term[] subs = new Term[2];
        subs[1] = tf.createVariableTerm(pv);
        if (term.arity() == 0) {
            subs[0] = term;
            return tf.createArrayTerm(ArrayOp.getArrayOp(term.sort()), subs);
        } else {
            if (term.sub(0).op() instanceof NonRigidFunctionLocation) {
                subs[0] = trh.getReadRep(term.sub(0).op());

            } else {
                subs[0] = term.sub(0);
            }
            return tf.createArrayTerm(ArrayOp.getArrayOp(term.sub(0).sort()),
                    subs);
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.key.unittest.AbstractTermRepresentation#createReadRep()
     */
    protected Term createReadRep() {
        pvRead = getPV((LogicVariable) left.sub(1).op());
        pvWrite = getPV((LogicVariable) left.sub(1).op());
        return createArrayAcc(left, pvRead);
    }

    /**
     * This method 'converts' a LogicVariable to a ProgramVariable
     * 
     * @param lv
     *            the LogicVariable to convert
     * @return the created ProgramVariable
     */
    private ProgramVariable getPV(LogicVariable lv) {
        return new LocationVariable(createNewName(lv.name().toString()), Main
                .getInstance().mediator().getJavaInfo().getTypeByName("int"));
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.key.unittest.AbstractTermRepresentation#getWriteRep()
     */
    public Statement getWriteRep() {
        final Expression lhs = tce.convertToProgramElement(readRep);
        final Expression rhs = tce.convertToProgramElement(createArrayAcc(right
                .sub(0), pvWrite));
        final LocationVariable length = new LocationVariable(
                new ProgramElementName("length"), pvWrite.getKeYJavaType());
        final Expression bound = tce.convertToProgramElement(tf
                .createAttributeTerm(length, getReadRep().sub(0)));
        return new For(new LoopInitializer[] { new CopyAssignment(pvWrite,
                new IntLiteral(0)) }, new LessThan(pvWrite, bound),
                new Expression[] { new PostIncrement(pvWrite) },
                new CopyAssignment(lhs, rhs));
    }

}
