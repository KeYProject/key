/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.proof.rulefilter;

import java.util.HashMap;
import java.util.LinkedHashMap;

import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.rules.Taclet;
import org.key_project.util.collection.ImmutableList;

/// Filter that selects taclets using the method <code>admissible</code> of the <code>Taclet</code>
/// class, i.e. with respect to active heuristics and the <code>interactive</code> flag. If the
/// interactive flag is set the following procedure is used: the non-interactive marked rules are
/// only taken if the given list of heuristics contains at least one heuristic of that rule. If the
/// interactive flag is not set, a rule is taken if the intersection between the given heuristics
/// and
/// the heuristics of the rule is not empty.
public class IHTacletFilter extends TacletFilter {

    /// @return true iff <code>this</code> taclet may be applied for the given mode
    /// (interactive/non-interactive, activated rule sets)
    public static boolean admissible(Taclet taclet, boolean interactive,
            ImmutableList<RuleSet> admissibleRuleSets) {
        if (interactive) {
            return true;
        } else {
            return taclet.getRuleSets().exists(admissibleRuleSets::contains);
        }
    }

    private final boolean interactive;
    private final ImmutableList<RuleSet> heuristics;

    private final HashMap<Taclet, Boolean> filterCache = new LinkedHashMap<>(2000);

    public IHTacletFilter(boolean interactive, ImmutableList<RuleSet> heuristics) {
        this.interactive = interactive;
        this.heuristics = heuristics;
    }

    /// @return true iff <code>taclet</code> should be included in the result
    public boolean filter(Taclet taclet) {
        if (!interactive) {
            Boolean b = filterCache.get(taclet);
            if (b == null) {
                b = admissible(taclet, interactive, heuristics) ? Boolean.TRUE : Boolean.FALSE;
                filterCache.put(taclet, b);
            }
            return b.equals(Boolean.TRUE);
        }
        // in interactive case we do not need to cache; the user is too slow ;-)
        return admissible(taclet, interactive, heuristics);
    }
}
