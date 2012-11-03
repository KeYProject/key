package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.Term;

public class LoopInvariantApplicationData {
    public final Term self;
    public final ImmutableList<Term> localIns;
    public final Term heapAtPre;
    public final ImmutableList<Term> localOuts;
    public final Term heapAtPost;
    
    public LoopInvariantApplicationData(Term self,
                                        ImmutableList<Term> localIns,
                                        Term preHeap,
                                        ImmutableList<Term> localOuts,
                                        Term postHeap) {
        this.heapAtPre = preHeap;
        this.self = self;
        this.localIns = localIns;
        this.localOuts = localOuts;
        this.heapAtPost = postHeap;
    }
    
    public LoopInvariantApplicationData(Term self,
                                        Term[] localIns,
                                        Term preHeap,
                                        Term[] localOuts,
                                        Term postHeap) {
        this(self, ImmutableSLList.<Term>nil().append(localIns), preHeap,
                ImmutableSLList.<Term>nil().append(localOuts), postHeap);
    }
}
