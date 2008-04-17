// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.proof;


import java.util.Stack;



/** Proof-specific counter object: taclet names, var names, node numbers, &c */
public class Counter {

    private String name;
    private int count;
    
    private Stack<NodeAnchor> undoAnchors = new Stack<NodeAnchor>();

    public Counter(String name) {
        this.name=name;
    }
    
    public int getCount() {
        return count;
    }

    public int getCountPlusPlus(Node undoAnchor) {
        undoAnchors.push(new NodeAnchor(undoAnchor));
        return count++;
    }
    
    public int getCountPlusPlusWithParent(Node undoAnchor) {
        undoAnchors.push(new NodeAnchor(undoAnchor, true));
        return count++;
    }
    
    public void undo(Node node) {
        if (undoAnchors.size()==0) {
            de.uka.ilkd.key.util.Debug.assertTrue(count==0,
                                        "No undoAnchor, count should be 0");
            return;
        }
        NodeAnchor anchor = (NodeAnchor)undoAnchors.peek();
        if ((!anchor.anchorIsParent() && anchor.node() == node) ||
                (anchor.anchorIsParent() && anchor.node() == node.parent())) {
            undoAnchors.pop();
            count--;
        }
    }
    
    public String toString() {
        return "Counter "+ name + ": " + count;
    }
    
    private static class NodeAnchor {
        Node node;
        boolean anchorIsParent = false;
        NodeAnchor(Node n) {
            node = n;       
        }
        NodeAnchor(Node n, boolean anchorIsChild) {
            node = n;       
            this.anchorIsParent=anchorIsChild;
        }
        Node node() {
            return node;
        }
        boolean anchorIsParent() {
            return anchorIsParent;
        }
    }

}
