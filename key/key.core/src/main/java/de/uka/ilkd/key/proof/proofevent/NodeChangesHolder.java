package de.uka.ilkd.key.proof.proofevent;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.SequentChangeInfo;


public class NodeChangesHolder {
    public ImmutableList<SequentChangeInfo> scis;

    NodeChangesHolder() {
        this(ImmutableSLList.<SequentChangeInfo>nil());
    }

    NodeChangesHolder(ImmutableList<SequentChangeInfo> p_scis) {
        scis = p_scis;
    }

    public void addSCI(SequentChangeInfo p_sci) {
        scis = scis.prepend(p_sci);
    }

    public Object clone() {
        return new NodeChangesHolder(scis);
    }
}
