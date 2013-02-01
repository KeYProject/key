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


package de.uka.ilkd.key.rule.conditions;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableMapEntry;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.LabelCollector;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This variable condition ensures that no other label of the
 * same name exists in the context program or one of the schemavariable
 * instantiations.
 */
public final class NewJumpLabelCondition implements VariableCondition {

    private final ProgramSV labelSV;
    
    public NewJumpLabelCondition(SchemaVariable sv) {        
        if (!(sv instanceof ProgramSV) || 
                ((ProgramSV)sv).sort() != ProgramSVSort.LABEL) {
            throw new IllegalArgumentException("The new jump label " +
                        "variable condition, must be parameterised with a " +
                        "program schemavariable of sort LABEL.");
        }
        
        labelSV = (ProgramSV) sv;
    }
    
    @Override
    public MatchConditions check(SchemaVariable var,
            SVSubstitute instCandidate, MatchConditions matchCond,
            Services services) {
        if (var != labelSV && 
                matchCond.getInstantiations().isInstantiated(labelSV)) { 
            var = labelSV;
            instCandidate = 
                (SVSubstitute) matchCond.getInstantiations().getInstantiation(labelSV);            
        }
        
        if (var == labelSV) {   
            if (!(instCandidate instanceof Label)) {                
                return null;
            }                       
            final List<ProgramElement> programs = collect(matchCond.getInstantiations());
            programs.add(matchCond.getInstantiations().getContextInstantiation().contextProgram());
            if (!isUnique((Label)instCandidate, programs, services)) {                                
                return null;
            }
        }    
        return matchCond;
    }

    private List<ProgramElement> collect(SVInstantiations inst) {
        final List<ProgramElement> result = new LinkedList<ProgramElement>();
        final Iterator<ImmutableMapEntry<SchemaVariable,InstantiationEntry>> 
            it = inst.pairIterator();
        while (it.hasNext()) {
            final ImmutableMapEntry<SchemaVariable,InstantiationEntry> entry = it.next();            
            if (entry.key() != labelSV && 
                    entry.value() != null && 
                    entry.value().getInstantiation() instanceof ProgramElement) {               
                result.add((ProgramElement) entry.value().getInstantiation());
            }
        }
        return result;
    }
    
    private boolean isUnique(Label label, 
                             List<ProgramElement> programs, 
                             Services services) {
        for (final ProgramElement pe : programs) {
            final LabelCollector lc = new LabelCollector(pe, services); 
            lc.start();
            if (lc.contains(label)) {
                return false;
            }
        }                             
        return true;       
    }

    
    @Override    
    public String toString() {
        return "\\newLabel (" +labelSV+ ")";
    }
}
    
