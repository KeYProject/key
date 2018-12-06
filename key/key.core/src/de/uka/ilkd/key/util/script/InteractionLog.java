package de.uka.ilkd.key.util.script;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
public class InteractionLog implements Serializable {
    private List<Interaction> interactions = new ArrayList<>();

    public List<Interaction> getInteractions() {
        return interactions;
    }

    public void setInteractions(List<Interaction> interactions) {
        this.interactions = interactions;
    }
}
