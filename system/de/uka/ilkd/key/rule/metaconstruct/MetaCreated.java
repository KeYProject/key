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
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Location;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.KeYSemanticException;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/** this class implements the interface for
 * MetaAdderators. MetaAdderators are used to do complex term
 * transformation when applying a taclet. Often these transformation
 * caanot be described with the taclet scheme (or trying to do so would
 * result in a huge number of rules)
 */
public class MetaCreated extends MetaField implements Location {

    public MetaCreated() {
	super("#created", false);
    }

    /** calculates the resulting term. 
     * @throws KeYSemanticException */
    public Term calculate(Term term, SVInstantiations svInst, 
			  Services services) {	
  
        final Term t = term.sub(0);
      
        final KeYJavaType objectKJT = services.getJavaInfo().getJavaLangObject();
        if (!(t.sort().extendsTrans(objectKJT.getSort()))) {
           
            throw new RuntimeException("Error:" + this + ". Rules have to ensure that" +
                    "this meta operator is only applied on subtypes of java.lang.Object" +
                    ", but this is of type " + t.sort() );
        }
        
        return termFactory.createAttributeTerm(services.getJavaInfo().
                getAttribute(ImplicitFieldAdder.IMPLICIT_CREATED, objectKJT), t);
    }

 
    public boolean mayBeAliasedBy(Location loc) {
        return true;
    }

    public Sort sort() {        
        return METASORT;
    }

}
