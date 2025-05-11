/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.*;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.BuiltInRuleAppIndex;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.scripts.meta.Option;
import de.uka.ilkd.key.scripts.meta.Varargs;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;
import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

/**
 * Command that applies a calculus rule All parameters are passed as strings and converted by the
 * command. The parameters are:
 * <ol>
 * <li>#2 = <String>rule name</String></li>
 * <li>on= key.core.logic.Term on which the rule should be applied to as String (find part of the
 * rule)</li>
 * <li>formula= toplevel formula in which term appears in</li>
 * <li>occ = occurrence number</li>
 * <li>inst_= instantiation</li>
 * </ol>
 */
public class RuleCommand extends AbstractCommand<RuleCommand.Parameters> {

    public RuleCommand() {
        super(Parameters.class);
    }

    @Override
    public @NonNull String getName() {
        return "rule";
    }

    @Override
    public @NonNull String getDocumentation() {
        return """
                Command that applies a calculus rule.
                All parameters are passed as strings and converted by the command.

                The parameters are:
                <ol>
                    <li>#2 = <String>rule name</String></li>
                    <li>on= key.core.logic.Term on which the rule should be applied to as String (find part of the rule) </li>
                    <li>formula= toplevel formula in which term appears in</li>
                    <li>occ = occurrence number</li>
                    <li>inst_= instantiation</li>
                </ol>
                """;
    }

    @Override
    public Parameters evaluateArguments(@NonNull EngineState state, Map<String, Object> arguments)
            throws Exception {
        return state.getValueInjector().inject(this, new Parameters(), arguments);
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, @NonNull Parameters args,
            EngineState state)
            throws ScriptException, InterruptedException {
        RuleApp theApp = makeRuleApp(args, state);
        Goal g = state.getFirstOpenAutomaticGoal();

        if (theApp instanceof TacletApp tacletApp) {

            if (!tacletApp.ifInstsComplete()) {
                ImmutableList<TacletApp> ifSeqCandidates =
                    tacletApp.findIfFormulaInstantiations(g.sequent(), g.proof().getServices());

                if (ifSeqCandidates.size() == 1) {
                    theApp = ifSeqCandidates.head();
                    assert theApp != null;
                    tacletApp = (TacletApp) theApp;
                }
            }

            RuleApp completeApp = tacletApp.tryToInstantiate(g.proof().getServices());
            theApp = completeApp == null ? theApp : completeApp;
        }
        assert theApp != null;

        g.apply(theApp);
    }

    private @Nullable RuleApp makeRuleApp(@NonNull Parameters p, @NonNull EngineState state)
            throws ScriptException {

        final Proof proof = state.getProof();
        final Optional<BuiltInRule> maybeBuiltInRule =
            proof.getInitConfig().getProfile().getStandardRules().standardBuiltInRules().stream()
                    .filter(r -> r.name().toString().equals(p.rulename)).findAny();

        final Optional<Taclet> maybeTaclet = Optional.ofNullable(
            proof.getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name(p.rulename)));

        if (!maybeBuiltInRule.isPresent() && !maybeTaclet.isPresent()) {
            /*
             * (DS, 2019-01-31): Might be a locally introduced taclet, e.g., by hide_left etc.
             */
            final Optional<TacletApp> maybeApp = Optional.ofNullable(
                state.getFirstOpenAutomaticGoal().indexOfTaclets().lookup(p.rulename));

            TacletApp app = maybeApp.orElseThrow(
                () -> new ScriptException("Taclet '" + p.rulename + "' not known."));

            if (app.taclet() instanceof FindTaclet) {
                app = findTacletApp(p, state);
            }

            return app;
        }

        if (maybeTaclet.isPresent()) {
            TacletApp theApp;
            if (maybeTaclet.get() instanceof NoFindTaclet) {
                theApp = makeNoFindTacletApp(maybeTaclet.get());
            } else {
                theApp = findTacletApp(p, state);
            }

            return instantiateTacletApp(p, state, proof, theApp);
        } else {
            IBuiltInRuleApp builtInRuleApp = //
                builtInRuleApp(p, state, maybeBuiltInRule.get());
            if (builtInRuleApp.isSufficientlyComplete()) {
                builtInRuleApp = builtInRuleApp.forceInstantiate(state.getFirstOpenAutomaticGoal());
            }
            return builtInRuleApp;
        }
    }

    private @Nullable TacletApp instantiateTacletApp(final @NonNull Parameters p,
            final @NonNull EngineState state,
            final @NonNull Proof proof, final @NonNull TacletApp theApp) throws ScriptException {
        TacletApp result;

        Services services = proof.getServices();
        ImmutableList<TacletApp> assumesCandidates = theApp
                .findIfFormulaInstantiations(state.getFirstOpenAutomaticGoal().sequent(), services);

        assumesCandidates = ImmutableList.fromList(filterList(p, assumesCandidates));

        if (assumesCandidates.size() != 1) {
            throw new ScriptException("Not a unique \\assumes instantiation");
        }

        result = assumesCandidates.head();

        /*
         * NOTE (DS, 2019-02-22): If we change something by instantiating the app as much as
         * possible, it might happen that the match conditions (those which are not really
         * conditions, but which change the instantiations based on others that are yet to be added)
         * have to be evaluated again, since the second call to tryToInstantiate won't do this if
         * everything already has been instantiated. That's a little sad and a border case, but I
         * had that problem.
         */
        boolean recheckMatchConditions;
        {
            /*
             * (DS, 2019-01-31): Try to instantiate first, otherwise, we cannot apply taclets with
             * "\newPV", Skolem terms etc.
             */
            final TacletApp maybeInstApp = result.tryToInstantiateAsMuchAsPossible(
                services.getOverlay(state.getFirstOpenAutomaticGoal().getLocalNamespaces()));

            if (maybeInstApp != null) {
                result = maybeInstApp;
                recheckMatchConditions = true;
            } else {
                recheckMatchConditions = false;
            }
        }

        recheckMatchConditions &= !result.uninstantiatedVars().isEmpty();

        for (SchemaVariable sv : result.uninstantiatedVars()) {
            if (result.isInstantiationRequired(sv)) {
                Term inst = p.instantiations.get(sv.name().toString());
                if (inst == null) {
                    throw new ScriptException("missing instantiation for " + sv);
                }

                result = result.addInstantiation(sv, inst, true, services);
            }
        }

        // try to instantiate remaining symbols
        result = result.tryToInstantiate(
            services.getOverlay(state.getFirstOpenAutomaticGoal().getLocalNamespaces()));

        if (result == null) {
            throw new ScriptException("Cannot instantiate this rule");
        }

        if (recheckMatchConditions) {
            final MatchConditions appMC =
                result.taclet().getMatcher().checkConditions(result.matchConditions(), services);
            if (appMC == null) {
                return null;
            } else {
                result = result.setMatchConditions(appMC, services);
            }
        }

        return result;
    }

    private @NonNull TacletApp makeNoFindTacletApp(@NonNull Taclet taclet) {
        return NoPosTacletApp.createNoPosTacletApp(taclet);
    }

    private IBuiltInRuleApp builtInRuleApp(@NonNull Parameters p, @NonNull EngineState state,
            @NonNull BuiltInRule rule)
            throws ScriptException {
        final List<IBuiltInRuleApp> matchingApps = //
            findBuiltInRuleApps(p, state).stream().filter(r -> r.rule().name().equals(rule.name()))
                    .toList();

        if (matchingApps.isEmpty()) {
            throw new ScriptException("No matching applications.");
        }

        if (p.occ < 0) {
            if (matchingApps.size() > 1) {
                throw new ScriptException("More than one applicable occurrence");
            }

            return matchingApps.get(0);
        } else {
            if (p.occ >= matchingApps.size()) {
                throw new ScriptException("Occurence " + p.occ
                    + " has been specified, but there are only " + matchingApps.size() + " hits.");
            }

            return matchingApps.get(p.occ);
        }
    }

    private TacletApp findTacletApp(@NonNull Parameters p, @NonNull EngineState state)
            throws ScriptException {

        ImmutableList<TacletApp> allApps = findAllTacletApps(p, state);
        List<TacletApp> matchingApps = filterList(p, allApps);

        if (matchingApps.isEmpty()) {
            throw new ScriptException("No matching applications.");
        }

        if (p.occ < 0) {
            if (matchingApps.size() > 1) {
                throw new ScriptException("More than one applicable occurrence");
            }
            return matchingApps.get(0);
        } else {
            if (p.occ >= matchingApps.size()) {
                throw new ScriptException("Occurence " + p.occ
                    + " has been specified, but there are only " + matchingApps.size() + " hits.");
            }
            return matchingApps.get(p.occ);
        }
    }

    private @NonNull ImmutableList<IBuiltInRuleApp> findBuiltInRuleApps(@NonNull Parameters p,
            @NonNull EngineState state)
            throws ScriptException {
        final Services services = state.getProof().getServices();
        final Goal g = state.getFirstOpenAutomaticGoal();
        final BuiltInRuleAppIndex index = g.ruleAppIndex().builtInRuleAppIndex();

        ImmutableList<IBuiltInRuleApp> allApps = ImmutableSLList.nil();
        for (SequentFormula sf : g.node().sequent().antecedent()) {
            if (!isFormulaSearchedFor(p, sf, services)) {
                continue;
            }

            allApps = allApps.append(
                index.getBuiltInRule(g, new PosInOccurrence(sf, PosInTerm.getTopLevel(), true)));
        }

        for (SequentFormula sf : g.node().sequent().succedent()) {
            if (!isFormulaSearchedFor(p, sf, services)) {
                continue;
            }

            allApps = allApps.append(
                index.getBuiltInRule(g, new PosInOccurrence(sf, PosInTerm.getTopLevel(), false)));
        }

        return allApps;
    }

    private @NonNull ImmutableList<TacletApp> findAllTacletApps(@NonNull Parameters p,
            @NonNull EngineState state)
            throws ScriptException {
        Services services = state.getProof().getServices();
        TacletFilter filter = new TacletNameFilter(p.rulename);
        Goal g = state.getFirstOpenAutomaticGoal();
        RuleAppIndex index = g.ruleAppIndex();
        index.autoModeStopped();

        ImmutableList<TacletApp> allApps = ImmutableSLList.nil();
        for (SequentFormula sf : g.node().sequent().antecedent()) {
            if (!isFormulaSearchedFor(p, sf, services)) {
                continue;
            }

            allApps = allApps.append(index.getTacletAppAtAndBelow(filter,
                new PosInOccurrence(sf, PosInTerm.getTopLevel(), true), services));
        }

        for (SequentFormula sf : g.node().sequent().succedent()) {
            if (!isFormulaSearchedFor(p, sf, services)) {
                continue;
            }

            allApps = allApps.append(index.getTacletAppAtAndBelow(filter,
                new PosInOccurrence(sf, PosInTerm.getTopLevel(), false), services));
        }

        return allApps;
    }

    /**
     * Returns true iff the given {@link SequentFormula} either matches the
     * {@link Parameters#formula} parameter or its String representation matches the
     * {@link Parameters#matches} regex. If both parameters are not supplied, always returns true.
     *
     * @param p The {@link Parameters} object.
     * @param sf The {@link SequentFormula} to check.
     * @return true if <code>sf</code> matches.
     */
    private boolean isFormulaSearchedFor(@NonNull Parameters p, @NonNull SequentFormula sf,
            @NonNull Services services) {
        final boolean satisfiesFormulaParameter =
            p.formula != null && sf.formula().equalsModProperty(p.formula, RENAMING_TERM_PROPERTY);

        final boolean satisfiesMatchesParameter = p.matches != null
                && formatTermString(LogicPrinter.quickPrintTerm(sf.formula(), services))
                        .matches(".*" + p.matches + ".*");

        return (p.formula == null && p.matches == null) || satisfiesFormulaParameter
                || satisfiesMatchesParameter;
    }

    /**
     * Removes spaces and line breaks from the string representation of a term.
     *
     * @param str The string to "clean up".
     * @return The original without spaces and line breaks.
     */
    private static @NonNull String formatTermString(@NonNull String str) {
        return str //
                .replace("\n", " ") //
                .replace(" +", " ");
    }

    /*
     * Filter those apps from a list that are according to the parameters.
     */
    private @NonNull List<TacletApp> filterList(@NonNull Parameters p,
            @NonNull ImmutableList<TacletApp> list) {
        List<TacletApp> matchingApps = new ArrayList<>();
        for (TacletApp tacletApp : list) {
            if (tacletApp instanceof PosTacletApp pta) {
                boolean add =
                    p.on == null || pta.posInOccurrence().subTerm()
                            .equalsModProperty(p.on, RENAMING_TERM_PROPERTY);

                Iterator<SchemaVariable> it = pta.instantiations().svIterator();
                while (it.hasNext()) {
                    SchemaVariable sv = it.next();
                    Term userInst = p.instantiations.get(sv.name().toString());
                    Object ptaInst =
                        pta.instantiations().getInstantiationEntry(sv).getInstantiation();

                    add &= userInst == null
                            || userInst.equalsModProperty(ptaInst, IRRELEVANT_TERM_LABELS_PROPERTY);
                }

                if (add) {
                    matchingApps.add(pta);
                }
            }
        }
        return matchingApps;
    }

    @SuppressWarnings("initialization")
    public static class Parameters {
        @Option(value = "#2")
        public String rulename;
        @Option(value = "on", required = false)
        @Nullable
        public Term on;
        @Option(value = "formula", required = false)
        @Nullable
        public Term formula;
        @Option(value = "occ", required = false)
        @Nullable
        public int occ = -1;
        /**
         * Represents a part of a formula (may use Java regular expressions as long as supported by
         * proof script parser). Rule is applied to the sequent formula which matches that string.
         */
        @Option(value = "matches", required = false)
        public @Nullable String matches = null;
        @Varargs(as = Term.class, prefix = "inst_")
        public @NonNull Map<String, Term> instantiations = new HashMap<>();
    }

    private static class TacletNameFilter extends TacletFilter {
        private final @NonNull Name rulename;

        public TacletNameFilter(@NonNull String rulename) {
            this.rulename = new Name(rulename);
        }

        @Override
        protected boolean filter(@NonNull Taclet taclet) {
            return taclet.name().equals(rulename);
        }
    }

}
