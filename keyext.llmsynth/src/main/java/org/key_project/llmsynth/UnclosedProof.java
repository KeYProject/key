package org.key_project.llmsynth;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * A Proof that could not be finished by key in the specified amount of steps.
 */
public class UnclosedProof {
    public final Proof proof;
    public ImmutableList<Name> programVariables;

    public UnclosedProof(Proof proof,
                         ImmutableList<ProgramVariable> programVariables) {
        this.proof = proof;
        this.programVariables = ImmutableSLList.nil();
        for (ProgramVariable var : programVariables) {
            this.programVariables = this.programVariables.append(var.name());
        }
    }
}
