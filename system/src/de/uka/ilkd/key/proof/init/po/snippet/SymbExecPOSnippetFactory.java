/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.logic.Term;

/**
 *
 * @author christoph
 */
public interface SymbExecPOSnippetFactory extends BasicPOSnippetFactory {

    /**
     * The snippets which can be produced by this factory.
     */
    public static enum Snippet {
        // [P] (heap = heapAtPost & self = selfAtPost & result = resultAtPost &
        //      exc = excAtPost)
        SYMBOLIC_EXEC (SymbolicExecutionSnippet.class);
        

        // type of the factory method
        public final Class c;
        
        // contructor
        Snippet(Class c) {
            this.c = c;
        }
    };


    public Term create(Snippet snippet)
            throws UnsupportedOperationException;

}
