// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * The meta operator inserting the proof obligation for the <tt>inReachableState</tt>
 * predicate
 * @see de.uka.ilkd.key.rule.metaconstruct.InReachableStatePOBuilder
 */
public class CreateInReachableStatePO extends AbstractMetaOperator {

    public CreateInReachableStatePO() {
        super(new Name("#createInReachableStatePO"), 1, Sort.FORMULA);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {   
        final InReachableStatePOBuilder po = new InReachableStatePOBuilder(services);
      
        return po.generatePO(term.sub(0));       
    }
    
   
}
