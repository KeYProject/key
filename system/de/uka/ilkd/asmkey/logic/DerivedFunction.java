// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.NonRigid;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;

/**
 * In the logic for ASM, we allow the definition of recursive
 * derived functions. (we use the same classes for the derived
 * predicate. cf. below).
 * This abstract class is used to contain everything but the
 * rigid(static)/nonrigid(dynamic) aspects that is done in 
 * the derived classes {@link RigidDerivedFunction} and 
 * {@link NonRigidDerivedFunction}. The reason is that
 * the non-rigid one should implement the {@link NonRigid} interface.
 * However, we use a factory-method to create the functions symbols
 * that are instancied with the correct subclass.
 */
public abstract class DerivedFunction extends Function {

    private FormalParameter[] args;
    private Term body;
    protected boolean isRec;
    
    protected DerivedFunction(Name name, Sort sort, FormalParameter[] args,
			      Term body, boolean isRecursive) {
	super(name, sort, FormalParameter.parametersAsSort(args));
	this.args = args;
	this.body = body;
	this.isRec = isRecursive;
    }

    public FormalParameter[] formalParameters() {
	return args;
    }
    
    public void setBody(Term term, Location location) throws ParserException {
	if (term.sort().equals(sort())) {
	    this.body = term;
	} else {
	    throw new ParserException("The body provided for the DerivedFunction " + name() +
				      " has sort=" + term.sort() + ";expected was sort=" + sort(),
				      location);
	}
    }

    public Term body() {
	return body;
    }
    
    public boolean isRecursive() {
	return isRec;
    }


    /*public static class FirstPassDerivedFunction extends DerivedFunction {
	public FirstPassDerivedFunction(Name name,
					Sort sort,
					FormalParameter[] args) {
	    super(name, sort, args, null, false);
	}
	}*/

}
