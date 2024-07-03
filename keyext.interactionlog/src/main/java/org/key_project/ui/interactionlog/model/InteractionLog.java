/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package org.key_project.ui.interactionlog.model;

import java.io.Serializable;
import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import javax.xml.bind.annotation.*;

import de.uka.ilkd.key.proof.Proof;

import org.key_project.ui.interactionlog.api.Interaction;
import org.key_project.util.RandomName;

/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
@XmlRootElement(name = "interaction-log")
@XmlAccessorType(XmlAccessType.FIELD)
public class InteractionLog implements Serializable {
    private static final long serialVersionUID = 1L;

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
