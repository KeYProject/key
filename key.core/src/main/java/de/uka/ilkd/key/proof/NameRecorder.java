package de.uka.ilkd.key.proof;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.Name;

public class NameRecorder {

    private ImmutableList<Name> pre = ImmutableSLList.<Name>nil();

    private ImmutableList<Name> post = ImmutableSLList.<Name>nil();

    public void setProposals(ImmutableList<Name> proposals) {
        pre = proposals;
    }

    public ImmutableList<Name> getProposals() {
        return post;
    }

    public void addProposal(Name proposal) {
        post = post.append(proposal);
    }

    public Name getProposal() {
        Name proposal = null;

        if (pre != null && !pre.isEmpty()) {
            proposal = pre.head();
            pre = pre.tail();
        }

        return proposal;
    }

    public NameRecorder copy() {
        final NameRecorder result = new NameRecorder();
        result.pre = pre;
        result.post = post;
        return result;
    }
}
