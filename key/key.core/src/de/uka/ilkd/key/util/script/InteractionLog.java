package de.uka.ilkd.key.util.script;

import com.sun.istack.internal.Nullable;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.util.RandomName;

import java.io.Serializable;
import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
public class InteractionLog implements Serializable {
    @Nullable
    private WeakReference<Proof> proof;

    private String name;

    private List<Interaction> interactions = new ArrayList<>();

    public InteractionLog() {
        this(RandomName.getRandomName());
    }

    public InteractionLog(String name) {
        this.name = name;
    }

    public InteractionLog(Proof proof) {
        this.proof = new WeakReference<>(proof);
    }

    public List<Interaction> getInteractions() {
        return interactions;
    }

    public void setInteractions(List<Interaction> interactions) {
        this.interactions = interactions;
    }
}
