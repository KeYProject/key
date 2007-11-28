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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/** this class implements the interface for
 * MetaAdderators. MetaAdderators are used to do complex term
 * transformation when applying a taclet. Often these transformation
 * cannot be described with the taclet scheme (or trying to do so would
 * result in a huge number of rules)
 */
public class MetaAttribute extends MetaField implements Location{

    private String attrName;

    public MetaAttribute() {
	super("#attribute");
    }

    public MetaAttribute(String attrName) {
	super("#attribute"+attrName);
	this.attrName = attrName;
    }

    /** calculates the resulting term. */
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(term.sub(0).sort());
        System.out.println("term.sub(0): "+term.sub(0));
        // This is still not really right, one would need something of the `@' notation thing
        return termFactory.createAttributeTerm
	    (services.getJavaInfo().getAllAttributes
	     (attrName, kjt).head(),
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
    
    public boolean mayBeAliasedBy(Location loc) {
        return true;
    }
    
    public MetaOperator getParamMetaOperator(String param) {
       MetaOperator mop = name2metaop("#attribute_"+param);
       if(mop != null)
         return mop;
       return new MetaAttribute(param);
    }

}
