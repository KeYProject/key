package org.key_project.rusty.rule.inst;

import org.key_project.logic.Term;
import org.key_project.rusty.logic.op.sv.OperatorSV;
import org.key_project.rusty.logic.op.sv.SchemaVariable;

public class TermInstantiation extends InstantiationEntry<Term> {
    private static final RigidnessException RIGIDNESS_EXCEPTION = new RigidnessException(
            "Tried to instantiate a rigid schema variable" + " with a non-rigid term/formula");


    /**
     * creates a new ContextInstantiationEntry
     *
     * @param sv the SchemaVariable that is instantiated
     * @param term the Term the SchemaVariable is instantiated with
     */
    TermInstantiation(SchemaVariable sv, Term term) {
        super(term);
        // TODO: Remove the check below and move it to the matching logic
        // Done for VM based matching
        if (sv instanceof OperatorSV asv && !term.isRigid() && asv.isRigid()) {
            throw RIGIDNESS_EXCEPTION;
        }
    }
}
