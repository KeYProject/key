/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.rule.NoPosTacletApp;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Name;
import org.key_project.prover.proof.rulefilter.RuleFilter;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

public interface ITacletIndex {
    /**
     * get all Taclets for the antecedent.
     *
     * @param pos the PosOfOccurrence describing the formula for which to look for top level taclets
     * @param filter Only return taclets the filter selects
     * @param services the Services object encapsulating information about the java datastructures
     *        like (static)types etc.
     * @return IList<NoPosTacletApp> containing all applicable rules and the corresponding
     *         instantiations to get the rule fit.
     */
    ImmutableList<NoPosTacletApp> getAntecedentTaclet(
            PosInOccurrence pos, RuleFilter filter, LogicServices services);

    /**
     * get all Taclets for the succedent.
     *
     * @param pos the PosOfOccurrence describing the formula for which to look for top level taclets
     * @param filter Only return taclets the filter selects
     * @param services the Services object encapsulating information about the java datastructures
     *        like (static)types etc.
     * @return IList<NoPosTacletApp> containing all applicable rules and the corresponding
     *         instantiations to get the rule fit.
     */
    ImmutableList<NoPosTacletApp> getSuccedentTaclet(
            PosInOccurrence pos, RuleFilter filter,
            LogicServices services);

    /**
     * get all Rewrite-Taclets.
     *
     * @param filter Only return taclets the filter selects
     * @param services the Services object encapsulating information about the java datastructures
     *        like (static)types etc.
     * @return IList<NoPosTacletApp> containing all applicable rules and the corresponding
     *         instantiations to get the rule fit.
     */
    ImmutableList<NoPosTacletApp> getRewriteTaclet(PosInOccurrence pos, RuleFilter filter,
            LogicServices services);

    /**
     * get all Taclets having no find expression.
     *
     * @param filter Only return taclets the filter selects
     * @param services the Services object encapsulating information about the java datastructures
     *        like (static)types etc.
     * @return IList<NoPosTacletApp> containing all applicable rules and an empty part for the
     *         instantiations because no instantiations are necessary.
     */
    ImmutableList<NoPosTacletApp> getNoFindTaclet(RuleFilter filter, LogicServices services);


    /**
     * returns a list with all partial instantiated no pos taclet apps
     *
     * @return list with all partial instantiated NoPosTacletApps
     */
    ImmutableList<NoPosTacletApp> getPartialInstantiatedApps();

    /**
     * returns a NoPosTacletApp whose Taclet has a name that equals the given name. If more Taclets
     * have the same name an arbitrary Taclet with that name is returned.
     *
     * @param name the name to lookup
     * @return the found NoPosTacletApp or null if no matching Taclet is there
     */
    NoPosTacletApp lookup(Name name);

    /**
     * returns a NoPosTacletApp whose Taclet has a name that equals the given name. If more Taclets
     * have the same name an arbitrary Taclet with that name is returned.
     *
     * @param name the name to lookup
     * @return the found NoPosTacletApp or null if no matching Taclet is there
     */
    @Nullable
    NoPosTacletApp lookup(String name);
}
