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
        INF_FLOW_INPUT_OUTPUT_RELATION (InfFlowInputOutputRelationSnippet.class),

        INF_FLOW_CONTRACT_APP_INOUT_RELATION (InfFlowContractAppInOutRelationSnippet.class),

        //     ( {s1}pre & {s2}pre )
        //  -> (   (   {s1}respects = {s2}respects
        //          &  {s1}declassifies = {s2}declassifies )
        //      -> {s1_post}respects = {s2_post}respects )
        INF_FLOW_CONTRACT_APPL (InfFlowContractAppSnippet.class),

        //     ( {s1}inv & {s2}inv )
        //  -> (   (   {s1}respects = {s2}respects )
        //          &  {s1}declassifies = {s2}declassifies )
        //      -> {s1_post}respects = {s2_post}respects )
        INF_FLOW_LOOP_INVARIANT_APPL (InfFlowLoopInvAppSnippet.class),

        //     {s1}EXECUTION_OF_package.class::m_WITH_PRE(self, param1, ..., paramN, heap, result, exc, heapAtPost)
        //  &  {s2}EXECUTION_OF_package.class::m_WITH_PRE(self, param1, ..., paramN, heap, result, exc, heapAtPost)
        SELFCOMPOSED_EXECUTION_WITH_PRE_RELATION (SelfcomposedExecutionSnippet.class),

        //      {s1}EXECUTION_OF_package.class::m_WITH_INV(self, localIn1, ..., localInN, heap,
        // localOut1, ..., localOutN, heapAtPost)
        //  &  {s2}EXECUTION_OF_package.class::m_WITH_WITH_INV(self, localIn1, ..., localInN, heap,
        // localOut1, ..., localOutN, heapAtPost)
        SELFCOMPOSED_LOOP_WITH_INV_RELATION (SelfcomposedLoopSnippet.class),

        SELFCOMPOSED_BLOCK_WITH_PRE_RELATION (SelfcomposedBlockSnippet.class);

        // type of the factory method
        public final Class<?> c;

        // constructor
        Snippet(Class<?> c) {
            this.c = c;
        }
    };


    public Term create(Snippet snippet)
            throws UnsupportedOperationException;

}