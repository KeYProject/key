package de.uka.ilkd.key.logic.label;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.TermLabel;
import de.uka.ilkd.key.rule.label.LoopBodyTermLabelInstantiator;
import de.uka.ilkd.key.rule.label.LoopInvariantNormalBehaviorTermLabelInstantiator;
import de.uka.ilkd.key.rule.label.SelectSkolemConstantTermLabelInstantiator;

public final class TermLabelUtil {

    private static final SymbolicExecutionTermLabelFactory SYMBEX_LABEL_FACTORY =
            new SymbolicExecutionTermLabelFactory();

    public static final Name ANON_HEAP_LABEL_NAME = new Name("anonHeapFunction");
    
    /**
     * Label attached to anonymisation heap function symbols as for instance
     * introduce in UseOperationContractRule or WhileInvariantRule.
     */
    public static final TermLabel ANON_HEAP_LABEL = 
            new SimpleTermLabel(ANON_HEAP_LABEL_NAME, null);
    
    public static final Name SELECT_SKOLEM_LABEL_NAME = new Name("selectSK");
    
    /**
     * Label attached to skolem constants introduced by the rule pullOutSelect.
     */
    public static final TermLabel SELECT_SKOLEM_LABEL = 
            new SimpleTermLabel(SELECT_SKOLEM_LABEL_NAME, 
                    SelectSkolemConstantTermLabelInstantiator.INSTANCE);

    public static final Name LOOP_BODY_LABEL_NAME = new Name("LoopBody");

    /**
     * Label attached to the modality which executes a loop body 
     * in branch "Body Preserves Invariant" of applied "Loop Invariant" rules. 
     */
    public static final TermLabel LOOP_BODY_LABEL =
            new SimpleTermLabel(LOOP_BODY_LABEL_NAME, LoopBodyTermLabelInstantiator.INSTANCE);
    
    public static final Name LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL_NAME = 
            new Name("LoopInvariantNormalBehavior");
    
    /**
     * Label attached to the implication when a loop body execution terminated
     * normally without any exceptions, returns or breaks
     * in branch "Body Preserves Invariant" of applied "Loop Invariant" rules
     * to show the loop invariant. 
     */
    public static final TermLabel LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL =
            new SimpleTermLabel(LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL_NAME,
                    LoopInvariantNormalBehaviorTermLabelInstantiator.INSTANCE);

    private TermLabelUtil() {
        // only static methods
    }

    public static void registerJavaTermLabels(TermLabelManager manager) {
        manager.addFactory(new SingletonLabelFactory<TermLabel>(ANON_HEAP_LABEL));
        manager.addFactory(new SingletonLabelFactory<TermLabel>(SELECT_SKOLEM_LABEL));
    }
    
    public static void registerSymbolicExecutionTermLabels(TermLabelManager manager) {
        manager.addFactory(new SingletonLabelFactory<TermLabel>(LOOP_BODY_LABEL));
        manager.addFactory(new SingletonLabelFactory<TermLabel>(LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL));
        manager.addFactory(SYMBEX_LABEL_FACTORY);
    }

}
