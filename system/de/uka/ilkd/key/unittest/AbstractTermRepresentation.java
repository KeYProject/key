// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;

/**
 * This class is needed for the Representation of NonRigidFunctionLocations
 * during Unit Test Generation
 * 
 * @author mbender
 * 
 */
public abstract class AbstractTermRepresentation {

    protected final Services serv;
    protected final AssignmentPair up;
    protected final TestCodeExtractor tce;
    protected final TermFactory tf;
    protected final TermRepHandler trh;
    protected final Term left;
    //protected final Term right;
    protected final Term readRep;

    public AbstractTermRepresentation(final AssignmentPair up,
	    final Services serv, final TestCodeExtractor tce,
	    final TermRepHandler trh) {
	left = up.locationAsTerm();
	//right = up.value();
	this.up = up;
	this.serv = serv;
	this.tce = tce;
	this.trh = trh;
	this.tf = TermFactory.DEFAULT;
	this.readRep = createReadRep();

    }

    protected abstract Term createReadRep();

    /**
     * This method returns a Term that allows to be exported while Test
     * Generation. It is used to get the corerct Representation in the
     * Postconditon of a Formula
     * 
     * @return the Representation
     */
    public Term getReadRep() {
	return readRep;
    }

    /**
     * This method returns a statement that is used during the initialisation of
     * generated Test-Files to initialize the represented NRFL
     * @param right the term that is written.
     * 
     * @return a Statement for initialization
     */
    public abstract Statement getWriteRep(Term right);

    protected ProgramElementName createNewName(final Term t) {
	return new ProgramElementName(cNewName(t));
    }

    protected ProgramElementName createNewName(final String t) {
	return new ProgramElementName(cNewName(t));
    }

    private String cNewName(final String t) {
	return "_" + t + "_" + TestGenFac.counter++;
    }

    private String cNewName(final Term t) {
	String result = cNewName(t.op().name().toString());
	Term sub;
	for (int i = 0; i < t.arity(); i++) {
	    sub = t.sub(i);
	    if (!(sub.op() instanceof LogicVariable)) {
		result += createNewName(sub);
	    }
	}
	return result;
    }

    @Override
    public String toString() {
	return up.toString();
    }
}
