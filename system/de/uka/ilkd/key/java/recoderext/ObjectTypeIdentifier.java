package de.uka.ilkd.key.java.recoderext;

import recoder.java.Identifier;

public class ObjectTypeIdentifier extends Identifier {
    
    public ObjectTypeIdentifier(String id) {
        super(id);
    }

    protected void setText(String text) {
        id = text.intern();
    }
    
    /**
     * Deep clone.
     * @return the object.
     */
    
    public ObjectTypeIdentifier deepClone() {
        return new ObjectTypeIdentifier(id);
    }
    
}