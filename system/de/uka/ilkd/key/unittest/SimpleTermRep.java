// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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
 * This class represents a NonRigidFunctionLocation without arguments
 * 
 * @author mbender
 * 
 */
public class SimpleTermRep extends AbstractTermRepresentation {

    /**
     * @param up
     * @param trh
     */
    public SimpleTermRep(AssignmentPair up, Services serv,
            TestCodeExtractor tce, TermRepHandler trh) {
        super(up, serv, tce, trh);
    }

    private Term createLocVar(Term term) {
        return tf.createVariableTerm(new LocationVariable(createNewName(term),
                serv.getJavaInfo().getKeYJavaType(term.sort())));
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
    @Override
    protected Term createReadRep() {
        return createLocVar(left);
    }

}
