// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.proof;





/** Proof-specific counter object: taclet names, var names, node numbers, &c */
public class Counter {

    private String name;
    private int count;
    
    /* This field seems to be useless. It introduces a memory leak because
     * sometimes there remains an NodeAnchor with a reference to a deleted Node (by prune proof)
     private Stack<NodeAnchor> undoAnchors = new Stack<NodeAnchor>();
     */

    public Counter(String name) {
        this.name=name;
    }
    
    public int getCount() {
        return count;
    }
    
    public int getCountPlusPlus(){
	return count++;
    }

    /**@deprecated
     */
    public int getCountPlusPlus(Node undoAnchor) {
//        undoAnchors.push(new NodeAnchor(undoAnchor));
        return count++;
    }
    
    /**@deprecated
     */
    public int getCountPlusPlusWithParent(Node undoAnchor) {
//        undoAnchors.push(new NodeAnchor(undoAnchor, true));
        return count++;
    }
    
    /**@deprecated
     */
    public void undo(Node node) {
/*        if (undoAnchors.size()==0) {
            de.uka.ilkd.key.util.Debug.assertTrue(count==0,
                                        "No undoAnchor, count should be 0");
            return;
        }
        NodeAnchor anchor = (NodeAnchor)undoAnchors.peek();
        if ((!anchor.anchorIsParent() && anchor.node() == node) ||
                (anchor.anchorIsParent() && anchor.node() == node.parent())) {
            System.out.println("Counter\""+name+"\".undo node.serialNr:"+anchor.node.serialNr);
            undoAnchors.pop();
            count--;
        }else{
            System.out.println("Counter\""+name+"\".undo FAILED: anchor.anchorIsParent()="+anchor.anchorIsParent()+
                    " anchor.node()==node="+(anchor.node()==node)+
                    " anchor.node()==node.parent()="+(anchor.node() == node.parent()));
        }
*/    }
    
    public String toString() {
        return "Counter "+ name + ": " + count;
    }
    
/*   
  See comment of the field "undoAnchors" above
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
*/
}
