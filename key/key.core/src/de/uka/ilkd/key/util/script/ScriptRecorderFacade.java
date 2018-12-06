package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;
import org.key_project.util.collection.ImmutableList;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @author Alexander Weigl <weigl@kit.edu>
 */
public class ScriptRecorderFacade {
    private static List<InteractionListeners> listeners = new ArrayList<>();
    private static Map<Proof, ScriptRecorderState> instances = new HashMap<>();

    public static ScriptRecorderState get(Proof proof) {
        return instances.computeIfAbsent(proof, key ->
                new ScriptRecorderState(proof)
        );
    }

    public static void runMacro(Node node, ProofMacro macro, PosInOccurrence posInOcc) {
        ScriptRecorderState state = get(node.proof());
        MacroInteraction interaction = new MacroInteraction(node, macro, posInOcc);
        state.getInteractions().add(interaction);
        emit(interaction);
    }

    public static void runBuiltIn(Goal goal, BuiltInRule rule, PosInOccurrence pos, boolean forced) {
        ScriptRecorderState state = get(goal.proof());
        NodeInteraction interaction = new BuiltInRuleInteraction(goal.node(), rule, pos);
        state.getInteractions().add(interaction);
        emit(interaction);
    }

    public static void addListener(InteractionListeners listener) {
        listeners.add(listener);
    }

    public static void removeListener(InteractionListeners listener) {
        listeners.remove(listener);
    }

    private static void emit(Interaction interaction) {
        listeners.forEach(l -> l.onInteraction(interaction));
    }

    public static void runAutoMode(Proof proof, ImmutableList<Goal> goals) {
        ScriptRecorderState state = get(proof);
        goals.stream().forEach(g -> {
            AutoModeInteraction interaction = new AutoModeInteraction(g.node());
            state.getInteractions().add(interaction);
            emit(interaction);
        });
    }

    public static void runRule(Goal goal, RuleApp app) {
        ScriptRecorderState state = get(goal.proof());
        RuleInteraction interaction = (new RuleInteraction(
                goal.node().parent(), app));
        state.getInteractions().add(interaction);
        emit(interaction);
    }
}
