// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/** this class implements the interface for
 * MetaAdderators. MetaAdderators are used to do complex term
 * transformation when applying a taclet. Often these transformation
 * caanot be described with the taclet scheme (or trying to do so would
 * result in a huge number of rules)
 */
public class MetaTransient extends AbstractMetaOperator {

    public MetaTransient() {
	super(new Name("#transient"), 1);
    }

    public boolean isRigid(Term t) {
	return false;
    }

    /**
     * checks whether the top level structure of the given @link Term
     * is syntactically valid, given the assumption that the top level
     * operator of the term is the same as this Operator. The
     * assumption that the top level operator and the term are equal
     * is NOT checked.  
     * @return true iff the top level structure of
     * the @link Term is valid.
     */
    public boolean validTopLevel(Term term) {
	// a meta operator accepts almost everything
	return term.arity() == arity();
    }


    /** calculates the resulting term. */
    public Term calculate(Term term, SVInstantiations svInst, Services services) {	
        return termFactory.createAttributeTerm
	    (services.getJavaInfo().getAttribute
	     (ImplicitFieldAdder.IMPLICIT_TRANSIENT, 
	             services.getJavaInfo().getJavaLangObject()),
	     term.sub(0));
    }

    /** (non-Javadoc)
     * by default meta operators do not match anything 
     * @see de.uka.ilkd.key.logic.op.Operator#match(SVSubstitute, de.uka.ilkd.key.rule.MatchConditions, de.uka.ilkd.key.java.Services)
     */
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {
        return null;
    }
}
