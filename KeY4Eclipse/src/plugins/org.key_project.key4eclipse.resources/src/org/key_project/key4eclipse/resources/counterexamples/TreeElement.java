package org.key_project.key4eclipse.resources.counterexamples;

import java.util.LinkedList;
import java.util.List;

public class TreeElement {
    
    private String label;
    private List<TreeElement> children;

    public TreeElement(String label) {
       this.label = label;
       this.children = new LinkedList<TreeElement>();
    }
    
    public void AddChild(TreeElement child){
        children.add(child);
    }

    public List<TreeElement> getChildren() {
       return children;
    }

    @Override
    public String toString() {
       return label;
    }
 }
