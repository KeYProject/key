// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Location;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/** this class implements the interface for
 * MetaAdderators. MetaAdderators are used to do complex term
 * transformation when applying a taclet. Often these transformation
 * caanot be described with the taclet scheme (or trying to do so would
 * result in a huge number of rules)
 */
public class MetaNextToCreate extends MetaField implements Location {

    public MetaNextToCreate() {
	super("#nextToCreate", false);
    }

    /** calculates the resulting term. 
     * @throws RuntimeException if <code>term.sub(0)</code> is not a sub term of Object
     */
    public Term calculate(Term term, SVInstantiations svInst, 
			  Services services) {	
  
        final Term t = term.sub(0);
        
        final Sort s = t.sort();      

        if (!(s instanceof ObjectSort)) {
            throw new RuntimeException("Wrong usage of meta operator " + this +
                    ". Sort of subterm is not an ObjectSort, but "+s);
        }
        return termFactory.createVariableTerm(services.getJavaInfo().
                getAttribute(ImplicitFieldAdder.IMPLICIT_NEXT_TO_CREATE, (ObjectSort)s));
    }

    public boolean mayBeAliasedBy(Location loc) {
        return true;
    }

    public Sort sort() {        
        return METASORT;
    }

}
