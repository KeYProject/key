package de.uka.ilkd.key.gui.interactionlog.model;

import de.uka.ilkd.key.proof.Proof;
import org.key_project.util.RandomName;

import javax.xml.bind.annotation.*;
import java.io.Serializable;
import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
@XmlRootElement(name = "interaction-log")
@XmlAccessorType(XmlAccessType.FIELD)
public class InteractionLog implements Serializable {
    @XmlTransient
    private WeakReference<Proof> proof;

    @XmlAttribute
    private String name;

    @XmlAttribute
    private Date created = new Date();

    private List<Interaction> interactions = new ArrayList<>();



    public InteractionLog() {
        this(RandomName.getRandomName());
    }

    public InteractionLog(String name) {
        this.name = name;
    }

    public InteractionLog(Proof proof) {
        int pos = Math.min(proof.name().toString().length(), 25);
        name = RandomName.getRandomName(" ")
                + " (" + proof.name().toString().substring(0, pos) + ")";
        this.proof = new WeakReference<>(proof);
    }

    public List<Interaction> getInteractions() {
        return interactions;
    }

    public void setInteractions(List<Interaction> interactions) {
        this.interactions = interactions;
    }

    @Override
    public String toString() {
        return name;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public Date getCreated() {
        return created;
    }

    public void setCreated(Date created) {
        this.created = created;
    }
}
