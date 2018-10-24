package de.uka.ilkd.key.logic.label;

import java.util.Iterator;
import java.util.Set;
import java.util.SortedSet;
import java.util.StringJoiner;
import java.util.TreeSet;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.logic.Name;

public class OriginTermLabel implements TermLabel {
    
    public final static Name NAME = new Name("Origin");
    
    private SortedSet<Origin> origins;
    
    public OriginTermLabel(Set<Origin> set) {
        this.origins = new TreeSet<>(set);
    }
    
    public OriginTermLabel(SpecType specType, PositionInfo posInfo) {
        this.origins = new TreeSet<>();
        this.origins.add(new Origin(specType, posInfo));
    }
    
    public OriginTermLabel(OriginTermLabel... labels) {
        this.origins = new TreeSet<>();
        
        for (OriginTermLabel label : labels) {
            this.origins.addAll(label.origins);
        }
    }
    
    @Override
    public String toString() {
        StringJoiner sj = new StringJoiner(", ", "" + NAME + "(", ")");
        
        for (Origin origin : origins) {
            sj.add(origin.specType.toString());
        }
        
        return sj.toString();
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public Object getChild(int i) {
        if (i > getChildCount()) {
            return null;
        } else {
            Iterator<Origin> it = origins.iterator();
            
            for (; i > 0; --i) {
                it.next();
            }
            
            return it.next(); 
        }
    }

    @Override
    public int getChildCount() {
        return origins.size();
    }
    
    public static class Origin implements Comparable<Origin> {
        
        public final SpecType specType;
        public final PositionInfo posInfo;
        
        public Origin(SpecType specType, PositionInfo posInfo) {
            this.specType = specType;
            this.posInfo = posInfo;
        }
        
        @Override
        public String toString() {
            return "(" + specType + ", (" + posInfo + "))";
        }

        @Override
        public int compareTo(Origin other) {
            int result = specType.toString().compareTo(other.specType.toString());
            
            if (result == 0) {
                if (posInfo == null) {
                    if (other.posInfo == null) {
                        return 0;
                    } else {
                        return -1;
                    }
                } else if (other.posInfo == null) {
                    return 1;
                }
                
                result = posInfo.getFileName().compareTo(other.posInfo.getFileName());
                
                if (result == 0) {
                    result = posInfo.getStartPosition().compareTo(other.posInfo.getStartPosition());
                }
            }
            
            return result;
        }
    }
    
    public static enum SpecType {
        PRE("pre"),
        POST("post");
        
        private String name;
        
        private SpecType(String name) {
            this.name = name;
        }
        
        @Override
        public String toString() {
            return name;
        }
    }
}
