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
public interface InfFlowPOSnippetFactory {

    /**
     * The snippets which can be produced by this factory.
     */
    public static enum Snippet {
        //     (   {s1}respects = {s2}respects
        //      &  {s1}declassifies = {s2}declassifies )
        //  -> {s1_post}respects = {s2_post}respects
        INF_FLOW_POST (InfFlowPostSnippet.class),

        //     ( {s1}pre & {s2}pre )
        //  -> (   (   {s1}respects = {s2}respects
        //          &  {s1}declassifies = {s2}declassifies )
        //      -> {s1_post}respects = {s2_post}respects )
        INF_FLOW_CONTRACT_APPL (InfFlowContractAppSnippet.class),

        //     {s1}EXECUTION_OF_package.class::m_WITH_PRE(self, param1, ..., paramN, heap, result, exc, heapAtPost)
        //  &  {s2}EXECUTION_OF_package.class::m_WITH_PRE(self, param1, ..., paramN, heap, result, exc, heapAtPost)
        // or (for loop invariants)
        //      {s1}EXECUTION_OF_package.class::m_WITH_INV(self, localIn1, ..., localInN, heap,
        // localOut1, ..., localOutN, heapAtPost)
        //  &  {s2}EXECUTION_OF_package.class::m_WITH_WITH_INV(self, localIn1, ..., localInN, heap,
        // localOut1, ..., localOutN, heapAtPost)
        SELFCOMPOSED_EXECUTION_WITH_PRE_RELATION (SelfcomposedExecutionSnippet.class);

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
