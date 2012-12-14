package de.uka.ilkd.key.logic.label;

import java.util.HashSet;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.ITermLabel;

public class TermLabelOperations {

    public static ImmutableArray<ITermLabel> union(
            ImmutableArray<ITermLabel> left, ImmutableArray<ITermLabel> right) {
        final HashSet<ITermLabel> set = new LinkedHashSet<ITermLabel>();
        for (ITermLabel l : left) { 
            set.add(l);
        }
        for (ITermLabel l : right) { 
            set.add(l);
        }
        return new ImmutableArray<ITermLabel>(set.toArray(new ITermLabel[set.size()]));
    }

    public static ImmutableArray<ITermLabel> sub(
            ImmutableArray<ITermLabel> left, ImmutableArray<ITermLabel> right) {
        final HashSet<ITermLabel> set = new LinkedHashSet<ITermLabel>();
        for (ITermLabel l : left) { 
            set.add(l);
        }
        for (ITermLabel l : right) { 
            set.remove(l);
        }
        return new ImmutableArray<ITermLabel>(set.toArray(new ITermLabel[set.size()]));
    }

}
