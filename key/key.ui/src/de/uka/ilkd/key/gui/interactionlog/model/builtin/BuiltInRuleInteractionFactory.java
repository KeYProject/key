package de.uka.ilkd.key.gui.interactionlog.model.builtin;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.smt.RuleAppSMT;

import java.util.HashMap;
import java.util.Map;

interface Factory<T extends IBuiltInRuleApp> {
    BuiltInRuleInteraction create(T app, Node node);
}

/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
public class BuiltInRuleInteractionFactory {
    private static Map<Class<? extends IBuiltInRuleApp>, Factory<? extends IBuiltInRuleApp>> map = new HashMap<>();


    static {
        register(OneStepSimplifierRuleApp.class, OSSBuiltInRuleInteraction::new);
        register(ContractRuleApp.class, ContractBuiltInRuleInteraction::new);
        register(UseDependencyContractApp.class, UseDependencyContractBuiltInRuleInteraction::new);
        register(LoopContractInternalBuiltInRuleApp.class, LoopContractInternalBuiltInRuleInteraction::new);
        register(LoopInvariantBuiltInRuleApp.class, LoopInvariantBuiltInRuleInteraction::new);
        register(MergeRuleBuiltInRuleApp.class, MergeRuleBuiltInRuleInteraction::new);
        register(RuleAppSMT.class, SMTBuiltInRuleInteraction::new);
    }

    public static <T extends IBuiltInRuleApp> void
    register(Class<T> clazz, Factory<T> factory) {
        map.put(clazz, factory);
    }

    @SuppressWarnings("unchecked")
    public static <T extends IBuiltInRuleApp> Factory<T>
    get(T app) {
        return (Factory<T>) map.get(app.getClass());
    }


    public static <T extends IBuiltInRuleApp> BuiltInRuleInteraction
    create(Node node, T app) {
        Factory<T> factory = BuiltInRuleInteractionFactory.get(app);
        if (factory == null) {
            throw new IllegalStateException("No handler registered for built in rule: " + app.rule());
        }
        return factory.create(app, node);
    }
}