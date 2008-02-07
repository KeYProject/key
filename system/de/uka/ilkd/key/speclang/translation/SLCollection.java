package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;

public abstract class SLCollection {

    private final SLCollectionType type;

    // HACK for OCLCollection to work!
    public SLCollection() {
        this.type = null;
    }
    
    public SLCollection(SLCollectionType t) {
        Debug.assertTrue(t != null);
        this.type = t;
    }
    
    public SLCollectionType getType() {
        return type;
    }
    
    public boolean isType(SLCollectionType t) {
        return type.equals(t);
    }
    
    public abstract Sort getElementSort();
    
}
