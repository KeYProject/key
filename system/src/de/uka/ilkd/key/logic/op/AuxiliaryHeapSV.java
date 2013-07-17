// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.AuxiliaryTermLabel;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;


/** 
 * A schema variable that is used as placeholder for auxiliary heap skolem
 * constants.
 */  
public final class AuxiliaryHeapSV extends AbstractSV {

  
    AuxiliaryHeapSV(Name name, Sort s) {
        super(name, s, true, false);
    }
    
    
    @Override
    public MatchConditions match(SVSubstitute subst, 
	    			 MatchConditions mc,
	    			 Services services) {
        if (subst != null && subst instanceof Term) {
            Term t = (Term) subst;
            if (t.hasLabels() &&
                t.containsLabel(AuxiliaryTermLabel.INSTANCE) &&
                t.op().arity() == 0 &&
                t.op() instanceof Function &&
                // the following is more or less a hack to match only on
                // skolem constants introduced by select-rules
                t.toString().startsWith("selectOf")) {
                return addInstantiation((Term) subst, mc, services);
            }
        }
        Debug.out("FAILED. Schemavariable of this kind only match terms " +
                "with label 'auxiliary'.");
        return null;
    }
	
    
    @Override
    public String toString() {
        return toString("auxiliaryHeapVar");
    }
    
    
    @Override
    public String proofToString() {
	return "\\schemaVar \\auxiliaryHeapVar " + name() + ";\n";
    }    
}
