package de.uka.ilkd.key.logic.label;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.label.LoopBodyTermLabelInstantiator;
import de.uka.ilkd.key.rule.label.LoopInvariantNormalBehaviorTermLabelInstantiator;
import de.uka.ilkd.key.rule.label.SelectSkolemConstantTermLabelInstantiator;
import de.uka.ilkd.key.rule.label.TermLabelInstantiator;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;


/**
 * This class is used to configure TermLabelManagers.
 * 
 * If you create new labels, you can make them available to the system by
 * putting them into this class.
 * 
 * Here, all relevant instances are stored as constants.
 * 
 * <p>
 * The static method {@link #registerJavaTermLabels(TermLabelManager)} should
 * register all {@link TermLabelFactory} objects and global
 * {@link TermLabelInstantiator} objects which are to be present in a
 * {@link JavaProfile}.
 * 
 * <p>
 * The static method {@link #registerSymbolicExecutionTermLabels(TermLabelManager)}
 * should name those units which are available in symbolic exeuction profiles only.
 * 
 * <p>
 * If you create a new a {@link Profile} implementation, consider adding new 
 * static configuration methods. 
 * 
 * @see Profile
 * @author Mattias Ulbrich
 */
public final class TermLabels {

    // ---------- Symbolic Execution

    private static final SymbolicExecutionTermLabelFactory SYMBEX_LABEL_FACTORY =
            new SymbolicExecutionTermLabelFactory();

    // ---------- Anon Heap

    public static final Name ANON_HEAP_LABEL_NAME = new Name("anonHeapFunction");

    /**
     * Label attached to anonymisation heap function symbols as for instance
     * introduce in UseOperationContractRule or WhileInvariantRule.
     */
    public static final TermLabel ANON_HEAP_LABEL = 
            new SimpleTermLabel(ANON_HEAP_LABEL_NAME, null);

    // ---------- Select Skolem

    public static final Name SELECT_SKOLEM_LABEL_NAME = new Name("selectSK");

    /**
     * Label attached to skolem constants introduced by the rule pullOutSelect.
     */
    public static final TermLabel SELECT_SKOLEM_LABEL = 
            new SimpleTermLabel(SELECT_SKOLEM_LABEL_NAME, 
                    SelectSkolemConstantTermLabelInstantiator.INSTANCE);

    // ---------- Loop body

    public static final Name LOOP_BODY_LABEL_NAME = new Name("LoopBody");

    /**
     * Label attached to the modality which executes a loop body 
     * in branch "Body Preserves Invariant" of applied "Loop Invariant" rules. 
     */
    public static final TermLabel LOOP_BODY_LABEL =
            new SimpleTermLabel(LOOP_BODY_LABEL_NAME, LoopBodyTermLabelInstantiator.INSTANCE);

    // ---------- Loop invariant normal behaviour

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

    private TermLabels() {
        // only static methods
    }

    /**
     * Register term labels relevant for {@link JavaProfile} objects.
     * 
     * @param manager
     *            the manager to register to, not <code>null</code>
     */
    public static void registerJavaTermLabels(TermLabelManager manager) {
        manager.addFactory(new SingletonLabelFactory<TermLabel>(ANON_HEAP_LABEL));
        manager.addFactory(new SingletonLabelFactory<TermLabel>(SELECT_SKOLEM_LABEL));
    }

    /**
     * Register term labels relevant for {@link SymbolicExecutionJavaProfile}
     * objects.
     * 
     * @param manager
     *            the manager to register to, not <code>null</code>
     */
    public static void registerSymbolicExecutionTermLabels(TermLabelManager manager) {
        manager.addFactory(new SingletonLabelFactory<TermLabel>(LOOP_BODY_LABEL));
        manager.addFactory(new SingletonLabelFactory<TermLabel>(LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL));
        manager.addFactory(SYMBEX_LABEL_FACTORY);
    }

}
