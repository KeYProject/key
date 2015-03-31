package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.IllegalInstantiationException;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

public abstract class MatchSchemaVariableInstruction<SV extends SchemaVariable> extends Instruction<SV> {

    public MatchSchemaVariableInstruction(SV op) {
        super(op);
    }

    /**
     * Tries to add the pair <tt>(this,term)</tt> to the match conditions. If
     * successful the resulting conditions are returned, otherwise null. Failure
     * is possible e.g. if this schemavariable has been already matched to a
     * term <tt>t2</tt> which is not unifiable with the given term.
     */
    protected final MatchConditions addInstantiation(Term term, MatchConditions matchCond,
            Services services) {

        if (op.isRigid() && !term.isRigid()) {
            return null;
        }      

        final SVInstantiations inst = matchCond.getInstantiations();

        final Term t = inst.getTermInstantiation(op, inst.getExecutionContext(), services);
        if(t != null) {
            if(!t.equalsModRenaming(term)) {
                return null;
            } else {
                return matchCond;
            }
        } 

        try {           
            return matchCond.setInstantiations(inst.add(op, term, services));
        } catch (IllegalInstantiationException e) {
            Debug.out("FAILED. Exception thrown at sorted schema variable", e);
        }
        
        return null;
    }

   

}