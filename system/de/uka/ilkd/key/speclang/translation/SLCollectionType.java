package de.uka.ilkd.key.speclang.translation;

/**
 * This class represents a specific type of a collection (such as the ocl's set,
 * bag or sequence)
 * 
 */
public class SLCollectionType {

    public static final SLCollectionType SET = new SLCollectionType("Set");
    public static final SLCollectionType BAG = new SLCollectionType("Bag");
    public static final SLCollectionType SEQUENCE = new SLCollectionType("Sequence");
    
    
    private final String name;
    
    public SLCollectionType(String name) {
        this.name = name;
    }
    
    public String getName() {
        return this.name;
    }
    
    public boolean equals(Object t) {
        if (t instanceof SLCollectionType) {
            return this.name.equals(((SLCollectionType) t).getName());
        }
        return false;
    }
    
    public int hashCode() {
        return 37*19 + this.name.hashCode();
    }
}
