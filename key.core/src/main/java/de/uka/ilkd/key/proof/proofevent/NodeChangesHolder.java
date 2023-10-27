/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.proofevent;

import de.uka.ilkd.key.logic.SequentChangeInfo;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;


public class NodeChangesHolder {
    public ImmutableList<SequentChangeInfo> scis;

    NodeChangesHolder() {
        this(ImmutableSLList.nil());
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
