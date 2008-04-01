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

    private HashSet<Label> labels;
    
    public LabelCollector(ProgramElement root,                           
                          Services services) {
        super(root, services);        
        this.labels = new HashSet<Label>(20);
    }
    
    public boolean contains(Label l) {
        return labels.contains(l);
    }
    
    protected void doDefaultAction(SourceElement node) {        
        if (node instanceof Label) {
            labels.add((Label) node);           
        }
    }

    protected void doAction(ProgramElement node) {  
        if (node instanceof Label) {
            labels.add((Label) node);
        }
    }

}
