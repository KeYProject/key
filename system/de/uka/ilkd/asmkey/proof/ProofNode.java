// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.proof;


import java.util.List;

import de.uka.ilkd.asmkey.util.ArrayUtil;


public final class ProofNode {

    /** rules applied to the current proof node */
    private final List rules;

    /** children of this node in the proof tree */
    private final List children;


    ProofNode(ProofRule[] rules, ProofNode[] children) {
        this.rules = ArrayUtil.toList(rules);
        this.children = ArrayUtil.toList(children);
    }


    /** return the rules, that must be applied to the current proof
     * node */
    public List getRules() {
        return rules;
    }

    /** return the children of this node in the proof tree */
    public List getChildren() {
        return children;
    }

}
