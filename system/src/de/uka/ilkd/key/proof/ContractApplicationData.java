/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.Term;

/**
 *
 * @author christoph
 */
public class ContractApplicationData {

    public final Term self;
    public final ImmutableList<Term> params;
    public final Term heapAtPre;
    public final Term result;
    public final Term exception;
    public final Term heapAtPost;
    
    public ContractApplicationData(Term self,
                                   ImmutableList<Term> params,
                                   Term preHeap,
                                   Term result,
                                   Term exception,
                                   Term postHeap) {
        this.heapAtPre = preHeap;
        this.self = self;
        this.params = params;
        this.result = result;
        this.exception = exception;
        this.heapAtPost = postHeap;
    }
    
    public ContractApplicationData(Term self,
                                   Term[] params,
                                   Term preHeap,
                                   Term result,
                                   Term exception,
                                   Term postHeap) {
        this(self, ImmutableSLList.<Term>nil().append(params), preHeap,
             result, exception, postHeap);
    }
}
