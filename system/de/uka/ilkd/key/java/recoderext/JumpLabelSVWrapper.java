package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.SchemaVariable;

public class JumpLabelSVWrapper implements SVWrapper {

    private SchemaVariable label; 
    
    public JumpLabelSVWrapper(SchemaVariable l) {
        label = l;
    }
    
    public SchemaVariable getSV() {        
        return label;
    }

    public void setSV(SchemaVariable sv) {
        label = sv;        
    }
    
    public String toString() {
        return ""+label;
    }

}
