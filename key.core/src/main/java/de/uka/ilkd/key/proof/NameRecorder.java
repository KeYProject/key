/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.logic.Name;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

public class NameRecorder {

    private ImmutableList<Name> pre = ImmutableSLList.nil();

    private ImmutableList<Name> post = ImmutableSLList.nil();

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
