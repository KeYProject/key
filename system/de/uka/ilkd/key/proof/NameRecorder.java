// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.logic.ListOfName;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.SLListOfName;

public class NameRecorder {

    private ListOfName pre = SLListOfName.EMPTY_LIST;

    private ListOfName post = SLListOfName.EMPTY_LIST;

    public void setProposals(ListOfName proposals) {
        pre = proposals;
    }

    public ListOfName getProposals() {
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
