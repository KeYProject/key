package de.uka.ilkd.key.rule.conditions;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.LabelCollector;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This variable condition ensures that no other label of the
 * same name exists in the context program or one of the schemavariable
 * instantiations.
 */
public class NewJumpLabelCondition implements VariableCondition {

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
            final LinkedList programs = collect(matchCond.getInstantiations());
            programs.add(matchCond.getInstantiations().getContextInstantiation().contextProgram());
            if (!isUnique((Label)instCandidate, programs, services)) {                                
                return null;
            }
        }    
        return matchCond;
    }

    private LinkedList collect(SVInstantiations inst) {
        final LinkedList result = new LinkedList();
        final IteratorOfEntryOfSchemaVariableAndInstantiationEntry 
            it = inst.pairIterator();
        while (it.hasNext()) {
            final EntryOfSchemaVariableAndInstantiationEntry entry = it.next();            
            if (entry.key() != labelSV && 
                    entry.value() != null && 
                    entry.value().getInstantiation() instanceof ProgramElement) {               
                result.add(entry.value().getInstantiation());
            }
        }
        return result;
    }
    
    private boolean isUnique(Label label, 
                             LinkedList programs, 
                             Services services) {
        final HashSet result = new HashSet(100);
        for (final Iterator it = programs.iterator(); it.hasNext();) {
            final LabelCollector lc = 
                new LabelCollector((ProgramElement)it.next(), result, services); 
            lc.start();
        }                             
        return !result.contains(label);       
    }

    public String toString() {
        return "\\newLabel (" +labelSV+ ")";
    }
}
    