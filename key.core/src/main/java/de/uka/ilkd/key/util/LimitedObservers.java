/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.util;

import java.util.Map;
import java.util.Objects;
import java.util.concurrent.ConcurrentHashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.ApplicationRestriction;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;

/**
 * Factory for *limited* observer functions and the taclets relating them to their unlimited
 * counterpart, used by {@link de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator} (ramification /
 * data-group reasoning) and by the {@code .key} file parser (which resolves {@code $lmtd}-suffixed
 * operator names).
 * <p>
 * A limited observer {@code f$lmtd} is a fresh function symbol with the same signature as its
 * unlimited observer {@code f}, plus two taclets:
 * <ul>
 * <li>an unlimited-to-limited taclet {@code f(...) == f$lmtd(...)} (in the {@code limitObserver}
 * rule set), and</li>
 * <li>a limited-to-unlimited rewrite {@code f$lmtd(...) -> f(...)}.</li>
 * </ul>
 * The limited observer and its taclets are memoized per unlimited observer, so repeated requests
 * within (and across) proofs return the same symbol instances and taclet sets. The mapping is a
 * pure function of the observer, so it does not need a
 * {@code SpecificationRepository} instance — the maps were moved here when the repository was
 * disbanded (JMLtk front-end rewrite).
 */
public final class LimitedObservers {

    /**
     * Suffix appended to the program name of an observer to obtain the name of its limited
     * counterpart, e.g. {@code get$lmtd}.
     *
     * @see #limitObs(IObserverFunction, Services)
     */
    public static final String LIMIT_SUFFIX = "$lmtd";

    private static final Map<IObserverFunction, IObserverFunction> UNLIMITED_TO_LIMITED =
        new ConcurrentHashMap<>();
    private static final Map<IObserverFunction, IObserverFunction> LIMITED_TO_UNLIMITED =
        new ConcurrentHashMap<>();
    private static final Map<IObserverFunction, ImmutableSet<Taclet>> UNLIMITED_TO_LIMIT_TACLETS =
        new ConcurrentHashMap<>();

    private LimitedObservers() {
    }

    /**
     * Returns the limited counterpart of the passed observer function together with the taclets
     * relating it to its unlimited counterpart. The result is memoized, so repeated calls for the
     * same observer return the same (limited observer, taclet set) pair.
     *
     * @param obs the observer function to limit; must not itself already be a limited observer
     * @param services the corresponding services instance
     * @return a pair of the limited observer function and the taclets (unlimited-to-limited and
     *         limited-to-unlimited) for it
     */
    public static synchronized Pair<IObserverFunction, ImmutableSet<Taclet>> limitObs(
            IObserverFunction obs, Services services) {
        assert LIMITED_TO_UNLIMITED.get(obs) == null : " observer is already limited: " + obs;
        // TODO Was the exact class match "obs.getClass() != ObserverFunction.class" correctly
        // converted into IProgramMethod? Wojtek: I guess so, but why are IProgramMethods excluded
        // from limiting? This kills limiting for model methods...
        // if(!(obs instanceof IObserverFunction && !(obs instanceof IProgramMethod))) {
        //   return null;
        // }

        IObserverFunction limited = UNLIMITED_TO_LIMITED.get(obs);
        ImmutableSet<Taclet> taclets = UNLIMITED_TO_LIMIT_TACLETS.get(obs);

        if (limited == null) {
            final String baseName =
                ((ProgramElementName) obs.name()).getProgramName() + LIMIT_SUFFIX;
            final Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();
            limited = new ObserverFunction(baseName, obs.sort(), obs.getType(), heapSort,
                obs.getContainerType(), obs.isStatic(), obs.getParamTypes(),
                obs.getHeapCount(services), obs.getStateCount());
            UNLIMITED_TO_LIMITED.put(obs, limited);
            LIMITED_TO_UNLIMITED.put(limited, obs);

            assert taclets == null;
            taclets = DefaultImmutableSet.<Taclet>nil()
                    .add(getLimitedToUnlimitedTaclet(limited, obs, services))
                    .add(getUnlimitedToLimitedTaclet(limited, obs, services));
            UNLIMITED_TO_LIMIT_TACLETS.put(obs, taclets);
        }

        return new Pair<>(Objects.requireNonNull(limited), Objects.requireNonNull(taclets));
    }

    /**
     * Returns the unlimited counterpart of the passed (possibly limited) observer function, or the
     * passed function itself if it is not a known limited observer.
     *
     * @param obs the possibly limited observer
     * @return the unlimited observer, or {@code obs} if it is not limited
     */
    public static IObserverFunction unlimitObs(IObserverFunction obs) {
        IObserverFunction result = LIMITED_TO_UNLIMITED.get(obs);
        if (result == null) {
            result = obs;
        }
        return result;
    }

    private static String getUniqueNameForObserver(IObserverFunction obs) {
        var sb = new StringBuilder(obs.name().toString());

        if (obs.isStatic()) {
            sb.append("_static_");
        }

        for (KeYJavaType pType : obs.getParamTypes()) {
            sb.append(pType.getFullName());
        }

        return sb.toString();
    }

    private static Taclet getLimitedToUnlimitedTaclet(IObserverFunction limited,
            IObserverFunction unlimited, TermServices services) {
        final TermBuilder tb = services.getTermBuilder();
        assert limited.arity() == unlimited.arity();

        // create schema terms
        final JTerm[] subs = new JTerm[limited.arity()];
        for (int i = 0; i < subs.length; i++) {
            final TermSV argSV = SchemaVariableFactory.createTermSV(new Name("t" + i),
                limited.argSort(i), false, false);
            subs[i] = tb.var(argSV);
        }
        final JTerm limitedTerm = tb.func(limited, subs);
        final JTerm unlimitedTerm = tb.func(unlimited, subs);

        // create taclet
        final RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        tacletBuilder.setFind(limitedTerm);
        tacletBuilder.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableList.nil(), unlimitedTerm));
        tacletBuilder.setName(
            MiscTools.toValidTacletName("unlimit " + getUniqueNameForObserver(unlimited)));
        // tacletBuilder.addRuleSet(new RuleSet(new Name("unlimitObserver")));
        return tacletBuilder.getTaclet();
    }

    private static Taclet getUnlimitedToLimitedTaclet(IObserverFunction limited,
            IObserverFunction unlimited, TermServices services) {
        assert limited.arity() == unlimited.arity();

        final TermBuilder tb = services.getTermBuilder();
        // create schema terms
        final JTerm[] subs = new JTerm[limited.arity()];
        for (int i = 0; i < subs.length; i++) {
            final TermSV argSV = SchemaVariableFactory.createTermSV(new Name("t" + i),
                limited.argSort(i), false, false);
            subs[i] = tb.var(argSV);
        }
        final JTerm limitedTerm = tb.func(limited, subs);
        final JTerm unlimitedTerm = tb.func(unlimited, subs);

        // create taclet
        final RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        tacletBuilder.setFind(tb.func(unlimited, subs));
        final SequentFormula cf = new SequentFormula(tb.equals(limitedTerm, unlimitedTerm));
        final Sequent addedSeq =
            JavaDLSequentKit.createAnteSequent(ImmutableList.singleton(cf));
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(addedSeq,
            ImmutableList.nil(), tb.func(unlimited, subs)));
        tacletBuilder.setApplicationRestriction(
            new ApplicationRestriction(ApplicationRestriction.IN_SEQUENT_STATE));
        tacletBuilder.setName(
            MiscTools.toValidTacletName("limit " + getUniqueNameForObserver(unlimited)));
        tacletBuilder.addRuleSet(new RuleSet(new Name("limitObserver")));

        return tacletBuilder.getTaclet();
    }
}
