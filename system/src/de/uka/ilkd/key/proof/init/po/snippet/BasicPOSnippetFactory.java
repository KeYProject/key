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
public interface BasicPOSnippetFactory {

    /**
     * The snippets which can be produced by this factory.
     */
    public static enum Snippet {
        // free precondition (the "general assumption")
        FREE_PRE (BasicFreePreSnippet.class),
        
        // free precondition (the "general assumption")
        FREE_INV (BasicFreeInvSnippet.class),
        
        // precondition of the contract (without free precondition)
        CONTRACT_PRE (BasicPreconditionSnippet.class),

        // postcondition of the contract
        CONTRACT_POST (BasicPostconditionSnippet.class),
        
        // modifies of the contract
        CONTRACT_MOD (BasicModifiesSnippet.class),
        
        // dependencies of the contract
        CONTRACT_DEP (BasicDependsSnippet.class),
        
        // invariant of the loop
        LOOP_INV (BasicLoopInvariantSnippet.class),

        // [P] (heap = heapAtPost & self = selfAtPost & result = resultAtPost &
        //      exc = excAtPost)
        SYMBOLIC_EXEC (BasicSymbolicExecutionSnippet.class),

        //   FREE_PRE
        // & CONTRACT_PRE
        // & [P] (heap = heapAtPost & self = selfAtPost & result = resultAtPost &
        //        exc = excAtPost)
        SYMBOLIC_EXEC_WITH_PRE (BasicSymbolicExecutionWithPreconditionSnippet.class),

        LOOP_EXEC (BasicLoopExecutionSnippet.class),

        LOOP_EXEC_WITH_INV (BasicLoopExecutionWithInvariantSnippet.class),

        BLOCK_EXEC (BasicBlockExecutionSnippet.class),

        BLOCK_EXEC_WITH_PRE (BasicBlockExecutionWithPreconditionSnippet.class),

        // RELATED_BY_package.class::m(self, localIn1, ..., localInN, heap,
        // localOut1, ..., localOutN, result, exc, heapAtPost)
        // This predicate is semantically equivalent to:
        // [P] (heap = heapAtPost & self = selfAtPost & result = resultAtPost &
        //      exc = excAtPost)
        METHOD_CALL_RELATION (MethodCallPredicateSnippet.class),

        // RELATED_BY_package.class::m(self, localIn1, ..., LocalInN, heap,
        // localOut1, ..., LocalOutN, heapAtPost)
        // This predicate is semantically equivalent to:
        // [P] (heap = heapAtPost & self = selfAtPost & localOuts = localOutsAtPost)
        LOOP_CALL_RELATION (LoopCallPredicateSnippet.class),

        // EXECUTION_OF_package.class::m_WITH_PRE(self, param1, ..., paramN, heap, result, exc, heapAtPost)
        // RELATED_BY_package.class::m(self, localIn1, ..., localInN, heap, localOut1, ..., localOutN, result, exc, heapAtPost)
        // This predicate is semantically equivalent to:
        // [P] (heap = heapAtPost & self = selfAtPost & result = resultAtPost &
        //      exc = excAtPost)
        BLOCK_CALL_RELATION (BlockCallPredicateSnippet.class),

        // miscellaneous snippets
        SELF_NOT_NULL (BasicSelfNotNullSnippet.class),       // "self != null"
        SELF_CREATED (BasicSelfCreatedSnippet.class),        // "self.<created> = TRUE"
        SELF_EXACT_TYPE (BasicSelfExactTypeSnippet.class),   // "MyClass::exactInstance(self) = TRUE"
        PARAMS_OK (BasicParamsOkSnippet.class),              // the general assumption that all parameter
                                                             // arguments are valid
        MBY_AT_PRE_DEF (BasicMbyAtPreDefSnippet.class);      // initial value of measured_by clause
        

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
