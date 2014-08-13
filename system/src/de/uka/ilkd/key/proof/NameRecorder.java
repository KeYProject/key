// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
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

        if (!pre.isEmpty()) {
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