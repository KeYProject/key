/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;

import org.key_project.logic.Name;
import org.key_project.prover.proof.rulefilter.TacletFilter;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.reflection.ClassLoaderUtil;

import org.jspecify.annotations.NonNull;
import org.keyproject.key.api.data.KeyIdentifications.NodeTextId;
import org.keyproject.key.api.data.KeyIdentifications.TermActionId;
import org.keyproject.key.api.data.TermActionDesc;
import org.keyproject.key.api.data.TermActionKind;

/**
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
public class TermActionUtil {
    private static final Set<Name> CLUTTER_RULESETS =
        Set.of(new Name("notHumanReadable"),
            new Name("obsolete"),
            new Name("pullOutQuantifierAll"),
            new Name("pullOutQuantifierEx"));

    private static final Set<Name> CLUTTER_RULES = Set.of(
        new Name("cut_direct_r"),
        new Name("cut_direct_l"),
        new Name("case_distinction_r"),
        new Name("case_distinction_l"),
        new Name("local_cut"),
        new Name("commute_and_2"),
        new Name("commute_or_2"),
        new Name("boxToDiamond"),
        new Name("pullOut"),
        new Name("typeStatic"),
        new Name("less_is_total"),
        new Name("less_zero_is_total"),
        new Name("applyEqReverse"),

        // the following are used for drag'n'drop interactions
        new Name("eqTermCut"),
        new Name("instAll"),
        new Name("instEx"));
    private static final Set<String> FILTER_SCRIPT_COMMANDS = Set.of(
        "exit",
        "leave",
        "javascript",
        "skip",
        "macro",
        "rule",
        "script");

    private final PosInSequent pos;
    private final Goal goal;
    private final PosInOccurrence occ;

    private final List<TermActionDesc> actions = new ArrayList<>(1024);
    private final NodeTextId nodeTextId;

    private final HashMap<Integer, TacletApp> tacletRules = new LinkedHashMap<>();

    public TermActionUtil(@NonNull NodeTextId nodeTextId, @NonNull KeYEnvironment<?> env,
            @NonNull PosInSequent pos, @NonNull Goal goal, int caretPos) {
        this.pos = pos;
        this.goal = goal;
        this.nodeTextId = nodeTextId;
        occ = pos.getPosInOccurrence();
        ProofControl c = env.getUi().getProofControl();
        // final ImmutableList<BuiltInRule> builtInRules = c.getBuiltInRule(goal, occ);
        var macros = ClassLoaderUtil.loadServices(ProofMacro.class);
        for (ProofMacro macro : macros) {
            var id = new TermActionId(nodeTextId, pos.toString(),
                "macro:" + macro.getScriptCommandName(), caretPos);
            TermActionDesc ta = new TermActionDesc(id, macro.getName(), macro.getDescription(),
                macro.getCategory(), TermActionKind.Macro);
            add(ta);
        }
        ImmutableList<TacletApp> findTaclet = c.getFindTaclet(goal, occ);
        ImmutableList<? extends TacletApp> findTaclets =
            occ != null
                    ? goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE, occ,
                        goal.getOverlayServices())
                    : ImmutableList.of();
        ImmutableList<NoPosTacletApp> noFindTaclets =
            goal.ruleAppIndex().getNoFindTaclet(TacletFilter.TRUE, goal.getOverlayServices());


        for (TacletApp tacletApp : findTaclets) {
            if (!tacletApp.complete()) {
                continue;
            }
            var id = new TermActionId(nodeTextId, pos.toString(),
                "find:" + tacletApp.rule(), caretPos);
            TermActionDesc ta = new TermActionDesc(id, tacletApp.rule().displayName(),
                tacletApp.rule().toString(), "", TermActionKind.Taclet);
            var index = add(ta);

            tacletRules.put(index, tacletApp);
        }

        for (TacletApp tacletApp : noFindTaclets) {
            var id = new TermActionId(nodeTextId, pos.toString(),
                "nofind:" + tacletApp.rule(), caretPos);
            TermActionDesc ta = new TermActionDesc(id, tacletApp.rule().displayName(),
                tacletApp.rule().toString(), "", TermActionKind.Taclet);
            var index = add(ta);

            tacletRules.put(index, tacletApp);
        }
    }

    private int add(TermActionDesc ta) {
        var index = actions.size();
        actions.add(ta);
        return index;
    }

    /**
     * Removes RewriteTaclet from the list.
     *
     * @param list the IList<Taclet> from where the RewriteTaclet are removed
     * @return list without RewriteTaclets
     */
    private static ImmutableList<TacletApp> removeRewrites(
            ImmutableList<TacletApp> list) {
        ImmutableList<TacletApp> result = ImmutableSLList.nil();
        for (TacletApp tacletApp : list) {
            Taclet taclet = tacletApp.taclet();
            result = (taclet instanceof RewriteTaclet ? result : result.prepend(tacletApp));
        }
        return result;
    }

    public List<TermActionDesc> getActions() {
        return actions;
    }

    // Applies the action with the given `id` on the goal used to create this instance.
    // Returns `true` if the rule was found and applied, `false` otherwise.
    public boolean applyAction(TermActionId id, Services services) {
        for (int i = 0; i < actions.size(); i++) {
            var desc = actions.get(i);

            if (desc.commandId().id().equals(id.id())) {
                switch (desc.kind()) {
                    case Taclet:
                        var rule = tacletRules.get(i);
                        var inst = rule.setPosInOccurrence(occ, services);
                        goal.apply(inst);
                        break;
                    default:
                        throw new RuntimeException("not yet implemented");
                }

                return true;
            }
        }

        return false;
    }
}
