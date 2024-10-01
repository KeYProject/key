package org.key_project.rusty.logic;

import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.proof.Node;
import org.key_project.rusty.rule.TacletApp;
import org.key_project.util.collection.ImmutableList;

public class InnerVariableNamer extends VariableNamer {
    public InnerVariableNamer(Services services) {
        super(services);
    }

    @Override
    public ProgramVariable rename(ProgramVariable var, Goal goal, PosInOccurrence posOfFind) {
        return null;
    }


    @Override
    public String getProposal(TacletApp app, SchemaVariable var, Services services, Node undoAnchor, ImmutableList<String> previousProposals) {
        return "";
    }
}
