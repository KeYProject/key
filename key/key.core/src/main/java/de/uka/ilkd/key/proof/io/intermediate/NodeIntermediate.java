// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.io.intermediate;

import java.util.LinkedList;

/**
 * Node in an intermediate proof representation. Responsible for
 * storing information about children of nodes.
 * 
 * @author Dominic Scheurer
 */
public abstract class NodeIntermediate {
    
    private LinkedList<NodeIntermediate> children =
            new LinkedList<NodeIntermediate>();
    
    public LinkedList<NodeIntermediate> getChildren() {
        return children;
    }
    
    public void setChildren(LinkedList<NodeIntermediate> children) {
        this.children = children;
    }
    
    public void addChild(NodeIntermediate child) {
        this.children.add(child);
    }
}