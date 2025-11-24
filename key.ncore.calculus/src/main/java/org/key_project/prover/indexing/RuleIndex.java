/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.indexing;

import java.util.Set;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Name;
import org.key_project.prover.proof.rulefilter.RuleFilter;
import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public interface RuleIndex<Application extends RuleApp> extends Cloneable {

    /**
     * adds a set of NoPosTacletApp to this index
     *
     * @param tacletAppList the NoPosTacletApps to be added
     */
    void addTaclets(Iterable<Application> tacletAppList);

    /**
     * adds a new Taclet with instantiation information to this index. If rule instance is not known
     * rule is not added
     *
     * @param taclet the Taclet and its instantiation info to be added
     */
    void add(Rule taclet);

    /**
     * adds a new Taclet with instantiation information to this index. If rule instance is not known
     * rule is not added
     *
     * @param tacletApplication the Taclet and its instantiation info to be added
     */
    void add(Application tacletApplication);

    /**
     * removes a Taclet with the given instantiation information from this index.
     *
     * @param tacletApplication the Taclet and its instantiation info to be removed
     */
    void remove(Application tacletApplication);

    /**
     * removes the given NoPosTacletApps from this index
     *
     * @param tacletAppList the NoPosTacletApps to be removed
     */
    void removeTaclets(Iterable<Application> tacletAppList);

    /**
     * copies the index
     */
    RuleIndex<Application> copy();

    /**
     * clones the index
     */
    Object clone();

    /**
     * retrieves all {@link RuleApp}s managed by this index
     *
     * @return all {@link RuleApp}s managed by this index
     */
    @NonNull
    Set<Application> allNoPosTacletApps();

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
    ImmutableList<Application> getAntecedentTaclet(PosInOccurrence pos, RuleFilter filter,
            LogicServices services);

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
    ImmutableList<Application> getSuccedentTaclet(
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
    ImmutableList<Application> getRewriteTaclet(PosInOccurrence pos, RuleFilter filter,
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
    ImmutableList<Application> getNoFindTaclet(RuleFilter filter, LogicServices services);

    /**
     * returns a NoPosTacletApp whose Taclet has a name that equals the given name. If more Taclets
     * have the same name an arbitrary Taclet with that name is returned.
     *
     * @param name the name to lookup
     * @return the found NoPosTacletApp or null if no matching Taclet is there
     */
    Application lookup(Name name);

    /**
     * returns a NoPosTacletApp whose Taclet has a name that equals the given name. If more Taclets
     * have the same name an arbitrary Taclet with that name is returned.
     *
     * @param name the name to lookup
     * @return the found NoPosTacletApp or null if no matching Taclet is there
     */
    @Nullable
    Application lookup(String name);

    /**
     * returns an unmodifiable set with all partial instantiated no pos taclet apps
     *
     * @return set with all partial instantiated NoPosTacletApps
     */
    Set<Application> getPartialInstantiatedApps();
}
