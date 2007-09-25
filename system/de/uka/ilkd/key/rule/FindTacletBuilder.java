// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.Term;
/** Superclass of TacletBuilder objects that have a non-empty find clause.
 * This should be all of them except NoFindTacletBuilder.
 */

public abstract class FindTacletBuilder extends TacletBuilder {

    protected Term find=null;

    /**
     * checks that a SchemaVariable that is used to match pure variables
     * (this means bound variables) occurs at most once in a quantifier of the
     * ifs and finds and throws an exception otherwise
     */
    protected void checkBoundInIfAndFind() {
	final BoundUniquenessChecker ch = 
                new BoundUniquenessChecker(getFind(), ifSequent());
	if (!ch.correct()) {
	    throw new TacletBuilderException(this, 
                    "A bound SchemaVariable variables occurs twice "
	            +"in if and find.");
	}
    }

    /* Get the `find' term.  This could be a term or a formula for a
     * RewriteTaclet, but only a formula for an Antec/Succ Taclet.
     */
    public Term getFind() {
	return find;
    }

}
