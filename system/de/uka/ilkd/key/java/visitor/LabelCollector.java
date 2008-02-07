package de.uka.ilkd.key.java.visitor;

import java.util.HashSet;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;

/**
 * Collects all labels found in a given program.
 */
public class LabelCollector extends JavaASTVisitor {

    private HashSet labels;
    
    public LabelCollector(ProgramElement root, 
                          HashSet labels, 
                          Services services) {
        super(root, services);        
        this.labels = labels;
    }
    
    public boolean contains(Label l) {
        return labels.contains(l);
    }
    
    protected void doDefaultAction(SourceElement node) {        
        if (node instanceof Label) {
            labels.add(node);           
        }
    }

    protected void doAction(ProgramElement node) {  
        if (node instanceof Label) {
            labels.add(node);
        }
    }

}
