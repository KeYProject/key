/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;

import org.key_project.logic.Name;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.reflection.ClassLoaderUtil;

import org.jspecify.annotations.NonNull;
import org.keyproject.key.api.data.KeyIdentifications;
import org.keyproject.key.api.data.KeyIdentifications.NodeTextId;
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

    public TermActionUtil(@NonNull NodeTextId nodeTextId, @NonNull KeYEnvironment<?> env,
            @NonNull PosInSequent pos, @NonNull Goal goal) {
        this.pos = pos;
        this.goal = goal;
        this.nodeTextId = nodeTextId;
        occ = pos.getPosInOccurrence();
        ProofControl c = env.getUi().getProofControl();
        final ImmutableList<BuiltInRule> builtInRules = c.getBuiltInRule(goal, occ);
        var macros = ClassLoaderUtil.loadServices(ProofMacro.class);
        for (ProofMacro macro : macros) {
            var id = new KeyIdentifications.TermActionId(nodeTextId.nodeId(), pos.toString(),
                "macro:" + macro.getScriptCommandName());
            TermActionDesc ta = new TermActionDesc(id, macro.getName(), macro.getDescription(),
                macro.getCategory(), TermActionKind.Macro);
            add(ta);
        }
        ImmutableList<TacletApp> findTaclet = c.getFindTaclet(goal, occ);
        var find = removeRewrites(findTaclet)
                .prepend(c.getRewriteTaclet(goal, occ));
        var nofind = c.getNoFindTaclet(goal);


        for (TacletApp tacletApp : find) {
            var id = new KeyIdentifications.TermActionId(nodeTextId.nodeId(), pos.toString(),
                "find:" + tacletApp.rule());
            TermActionDesc ta = new TermActionDesc(id, tacletApp.rule().displayName(),
                tacletApp.rule().toString(), "", TermActionKind.Taclet);
            add(ta);
        }

        for (TacletApp tacletApp : nofind) {
            var id = new KeyIdentifications.TermActionId(nodeTextId.nodeId(), pos.toString(),
                "nofind:" + tacletApp.rule());
            TermActionDesc ta = new TermActionDesc(id, tacletApp.rule().displayName(),
                tacletApp.rule().toString(), "", TermActionKind.Taclet);
            add(ta);
        }
    }

    private void add(TermActionDesc ta) {
        actions.add(ta);
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
}
