//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2008 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.unittest;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;

/**
 * This class represents a NonRigidFunctionLocation beeing an attribute
 * @author mbender
 * 
 */
public class AttributeTermRep extends AbstractTermRepresentation {

    /**
     * @param up
     * @param serv
     * @param tce
     * @param trh
     */
    public AttributeTermRep(AssignmentPair up, Services serv,
            TestCodeExtractor tce, TermRepHandler trh) {
        super(up, serv, tce, trh);
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.key.unittest.AbstractTermRepresentation#getWriteRep()
     */
    public Statement getWriteRep() {
        final Expression l, r;
        l = tce.convertToProgramElement(readRep);
        r = tce.convertToProgramElement(right);
        return new CopyAssignment(l, r);
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.key.unittest.AbstractTermRepresentation#createReadRep()
     */
    protected Term createReadRep() {
        return tf.createVariableTerm(new LocationVariable(createNewName(left),
                serv.getJavaInfo().getKeYJavaType(left.sort())));
    }

}
