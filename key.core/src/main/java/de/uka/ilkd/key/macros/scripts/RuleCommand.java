/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.macros.scripts;

import java.io.StringReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.macros.scripts.meta.Description;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.Varargs;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.BuiltInRuleAppIndex;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.*;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Command that applies a calculus rule All parameters are passed as strings and
 * converted by the command. The parameters are:
 * <ol>
 * <li>#2 = <String>rule name</String></li>
 * <li>on= key.core.logic.Term on which the rule should be applied to as String
 * (find part of the rule)</li>
 * <li>formula= toplevel formula in which term appears in</li>
 * <li>occ = occurrence number</li>
 * <li>inst_= instantiation</li>
 * </ol>
 *
 * [scriptDoc "rule"]
 * This command can be used to apply a single calculus rule to the currently active
 * open goal.
 *
 * ### Parameters:
 *
 * [parameter "<1st>" "String"] The name of the rule to be applied
 * [parameter "on" "Term [optional]"] The term to be used as the "find" term in
 * a taclet with "find".
 * [parameter "occ" "int [optional]"] The number of the occurrence of *on* in case there
 * are several applicable rule apps
 * [parameter "formula" "Term [optional]"] The toplevel formula in which the
 * find clause is to be searched.
 * [parameter "matches" "String [optional]"] Instead of giving the toplevl formula
 * completely, a regular expression can be specified to match the toplevel formula.
 * [parameter "inst_SCHEMA" "Term [optional]"] If there are further schema variables
 * to be instantiated parameters prefixed with "inst_" can be added, e.g.
 * <tt>inst_b="true"</tt> if schema variable b is to be set to the formula true.
 * [/scriptDoc]
 */
public class RuleCommand extends AbstractCommand<RuleCommand.Parameters> {

    public RuleCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "rule";
    }

    @Override
    public Parameters evaluateArguments(EngineState state,
            Map<String, String> arguments) throws Exception {
        // TODO Is this not equivalent to the implementation in the superclass?
        return state.getValueInjector().inject(this, new Parameters(),
            arguments);
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Parameters args,
            EngineState state) throws ScriptException, InterruptedException {
        RuleApp theApp = makeRuleApp(args, state);
        Goal g = state.getFirstOpenAutomaticGoal();

        if (theApp instanceof TacletApp) {
            RuleApp completeApp = ((TacletApp) theApp).tryToInstantiate(g.proof().getServices());
            theApp = completeApp == null ? theApp : completeApp;
        }
        assert theApp != null;

        g.apply(theApp);
    }

    private RuleApp makeRuleApp(Parameters p, EngineState state)
            throws ScriptException {

        final Proof proof = state.getProof();
        final Optional<BuiltInRule> maybeBuiltInRule = proof.getInitConfig()
                .getProfile().getStandardRules().getStandardBuiltInRules()
                .stream().filter(r -> r.name().toString().equals(p.rulename))
                .findAny();

        final Optional<Taclet> maybeTaclet = Optional
                .ofNullable(proof.getEnv().getInitConfigForEnvironment()
                        .lookupActiveTaclet(new Name(p.rulename)));

        if (!maybeBuiltInRule.isPresent() && !maybeTaclet.isPresent()) {
            /*
             * (DS, 2019-01-31): Might be a locally introduced taclet, e.g., by
             * hide_left etc.
             */
            final Optional<TacletApp> maybeApp = Optional
                    .ofNullable(state.getFirstOpenAutomaticGoal()
                            .indexOfTaclets().lookup(p.rulename));

            TacletApp app = maybeApp.orElseThrow(() -> new ScriptException(
                "Taclet '" + p.rulename + "' not known."));

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
                builtInRuleApp = builtInRuleApp
                        .forceInstantiate(state.getFirstOpenAutomaticGoal());
            }
            return builtInRuleApp;
        }
    }

    private TacletApp instantiateTacletApp(final Parameters p,
            final EngineState state, final Proof proof, final TacletApp theApp)
            throws ScriptException {
        TacletApp result = theApp;

        Services services = proof.getServices();
        ImmutableList<TacletApp> assumesCandidates = theApp
                .findIfFormulaInstantiations(
                    state.getFirstOpenAutomaticGoal().sequent(), services);

        assumesCandidates = ImmutableList.fromList(filterList(p, assumesCandidates, services));

        if (assumesCandidates.size() == 0) {
            throw new ScriptException("No \\assumes instantiation");
        } else if (assumesCandidates.size() != 1) {
            throw new ScriptException("Not a unique \\assumes instantiation");
        }

        result = assumesCandidates.head();

        /*
         * NOTE (DS, 2019-02-22): If we change something by instantiating the
         * app as much as possible, it might happen that the match conditions
         * (those which are not really conditions, but which change the
         * instantiations based on others that are yet to be added) have to be
         * evaluated again, since the second call to tryToInstantiate won't do
         * this if everything already has been instantiated. That's a little sad
         * and a border case, but I had that problem.
         */
        boolean recheckMatchConditions;
        {
            /*
             * (DS, 2019-01-31): Try to instantiate first, otherwise, we cannot
             * apply taclets with "\newPV", Skolem terms etc.
             */
            final TacletApp maybeInstApp = result
                    .tryToInstantiateAsMuchAsPossible(services.getOverlay(state
                            .getFirstOpenAutomaticGoal().getLocalNamespaces()));

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
                String strInst = p.instantiations.get(sv.name().toString());
                if (strInst == null) {
                    throw new ScriptException(
                            "missing instantiation for " + sv);
                }

                var extns = result.extendVarNamespaceForSV(services.getNamespaces().variables(), sv);
                var nss = services.getNamespaces().copy();
                nss.setVariables(extns);
                Term inst = toTerm(services, nss, strInst);
                result = result.addInstantiation(sv, inst, true, services);
            }
        }

        // try to instantiate remaining symbols
        result = result.tryToInstantiate(services.getOverlay(
            state.getFirstOpenAutomaticGoal().getLocalNamespaces()));

        if (result == null) {
            throw new ScriptException("Cannot instantiate this rule");
        }

        if (recheckMatchConditions) {
            final MatchConditions appMC = result.taclet().getMatcher()
                    .checkConditions(result.matchConditions(), services);
            if (appMC == null) {
                return null;
            } else {
                result = result.setMatchConditions(appMC, services);
            }
        }

        return result;
    }

    private Term toTerm(Services services, NamespaceSet nss, String string) {
        var parser = new KeyIO(services, nss);
        return parser.parseExpression(string);
    }

    private TacletApp makeNoFindTacletApp(Taclet taclet) {
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(taclet);
        return app;
    }

    private IBuiltInRuleApp builtInRuleApp(Parameters p, EngineState state,
            BuiltInRule rule) throws ScriptException {
        final List<IBuiltInRuleApp> matchingApps = //
            findBuiltInRuleApps(p, state).stream()
                    .filter(r -> r.rule().name().equals(rule.name()))
                    .collect(Collectors.toList());

        if (matchingApps.isEmpty()) {
            throw new ScriptException("No matching applications.");
        }

        if (p.occ < 0) {
            if (matchingApps.size() > 1) {
                throw new ScriptException(
                    "More than one applicable occurrence");
            }

            return matchingApps.get(0);
        } else {
            if (p.occ >= matchingApps.size()) {
                throw new ScriptException("Occurrence " + p.occ
                    + " has been specified, but there are only " + matchingApps.size() + " hits.");

            }

            return matchingApps.get(p.occ);
        }
    }

    private TacletApp findTacletApp(Parameters p, EngineState state)
            throws ScriptException {

        ImmutableList<TacletApp> allApps = findAllTacletApps(p, state);
        List<TacletApp> matchingApps = filterList(p, allApps, state.getProof().getServices());

        if (matchingApps.isEmpty()) {
            throw new ScriptException("No matching applications.");
        }

        if (p.occ < 0) {
            if (matchingApps.size() > 1) {
                throw new ScriptException(
                    "More than one applicable occurrence");
            }
            return matchingApps.get(0);
        } else {
            if (p.occ >= matchingApps.size()) {
                throw new ScriptException("Occurence " + p.occ
                    + " has been specified, but there are only "
                    + matchingApps.size() + " hits.");
            }
            return matchingApps.get(p.occ);
        }
    }

    private ImmutableList<IBuiltInRuleApp> findBuiltInRuleApps(Parameters p,
            EngineState state) throws ScriptException {
        final Services services = state.getProof().getServices();
        assert services != null;

        final Goal g = state.getFirstOpenAutomaticGoal();
        final BuiltInRuleAppIndex index = g.ruleAppIndex()
                .builtInRuleAppIndex();

        ImmutableList<IBuiltInRuleApp> allApps = ImmutableSLList.nil();
        for (SequentFormula sf : g.node().sequent().antecedent()) {
            if (!isSequentFormulaSearchedFor(p, sf, services)) {
                continue;
            }

            allApps = allApps.append(index.getBuiltInRule(g,
                new PosInOccurrence(sf, PosInTerm.getTopLevel(), true)));
        }

        for (SequentFormula sf : g.node().sequent().succedent()) {
            if (!isSequentFormulaSearchedFor(p, sf, services)) {
                continue;
            }

            allApps = allApps.append(index.getBuiltInRule(g,
                new PosInOccurrence(sf, PosInTerm.getTopLevel(), false)));
        }

        return allApps;
    }

    private ImmutableList<TacletApp> findAllTacletApps(Parameters p,
            EngineState state) throws ScriptException {
        Services services = state.getProof().getServices();
        assert services != null;
        TacletFilter filter = new TacletNameFilter(p.rulename);
        Goal g = state.getFirstOpenAutomaticGoal();
        RuleAppIndex index = g.ruleAppIndex();
        index.autoModeStopped();

        ImmutableList<TacletApp> allApps = ImmutableSLList.nil();
        for (SequentFormula sf : g.node().sequent().antecedent()) {
            if (!isSequentFormulaSearchedFor(p, sf, services)) {
                continue;
            }

            allApps = allApps.append(index.getTacletAppAtAndBelow(filter,
                new PosInOccurrence(sf, PosInTerm.getTopLevel(), true),
                services));
        }

        for (SequentFormula sf : g.node().sequent().succedent()) {
            if (!isSequentFormulaSearchedFor(p, sf, services)) {
                continue;
            }

            allApps = allApps.append(index.getTacletAppAtAndBelow(filter,
                new PosInOccurrence(sf, PosInTerm.getTopLevel(), false),
                services));
        }

        return allApps;
    }

    /**
     * Returns true iff the given {@link SequentFormula} either matches the
     * {@link Parameters#formula} parameter or its String representation matches
     * the {@link Parameters#matches} regex. If both parameters are not
     * supplied, always returns true.
     *
     * @param p
     *        The {@link Parameters} object.
     * @param sf
     *        The {@link SequentFormula} to check.
     * @return true if <code>sf</code> matches.
     */
    private boolean isSequentFormulaSearchedFor(Parameters p, SequentFormula sf, Services services)
            throws ScriptException {
        final boolean satisfiesFormulaParameter =
            p.formula != null && sf.formula().equalsModRenaming(p.formula);

        final boolean satisfiesMatchesParameter = p.matches != null
                && formatTermString(
                    LogicPrinter.quickPrintTerm(sf.formula(), services))
                            .matches(".*" + p.matches + ".*");

        return (p.formula == null && p.matches == null)
                || satisfiesFormulaParameter || satisfiesMatchesParameter;
    }

    /**
     * Removes spaces and line breaks from the string representation of a term.
     *
     * @param str
     *        The string to "clean up".
     * @return The original without spaces and line breaks.
     */
    private static String formatTermString(String str) {
        return str //
                .replace("\n", " ") //
                .replace(" +", " ");
    }

    /*
     * Filter those apps from a list that are according to the parameters.
     */
    private List<TacletApp> filterList(Parameters p,
                                       ImmutableList<TacletApp> list, Services services) {
        List<TacletApp> matchingApps = new ArrayList<>();
        TermComparisonWithHoles tc = new TermComparisonWithHoles(services);

        for (TacletApp tacletApp : list) {
            boolean add = true;
            if (tacletApp instanceof PosTacletApp) {
                PosTacletApp pta = (PosTacletApp) tacletApp;
                add = p.on == null
                        || tc.compareModHoles(p.on, pta.posInOccurrence());

                Iterator<SchemaVariable> it = pta.instantiations().svIterator();
                while (it.hasNext()) {
                    SchemaVariable sv = it.next();
                    String str = p.instantiations.get(sv.name().toString());
                    Term userInst = null;
                    if(str != null) {
                        userInst = toTerm(services, services.getNamespaces(), str);
                    }
                    Object ptaInst =
                        pta.instantiations().getInstantiationEntry(sv).getInstantiation();

                    add &= userInst == null || userInst.equalsModIrrelevantTermLabels(ptaInst);
                }
            }

            if(tacletApp.ifFormulaInstantiations() != null)
                add &= checkAssumes(p, tacletApp.ifFormulaInstantiations(), services);

            if (add) {
                matchingApps.add(tacletApp);
            }

        }
        return matchingApps;
    }

    private boolean checkAssumes(Parameters p, ImmutableList<IfFormulaInstantiation> ifFormulaInstantiations, Services services) {
        if(p.assumes == null) {
            // no "assumes" restrictions specified.
            return true;
        }

        TermComparisonWithHoles tc = new TermComparisonWithHoles(services);
        if(!tc.containsModHoles(p.assumes, ifFormulaInstantiations)) {
            return false;
        }

        return true;
    }

    @Description(value = "Apply a calculus rule to the current goal.\nAdditional instantiations can be added as paramaters prefixed with inst_",
        examples = {
            "rule \"and_left\"",
            "rule \"and_left\" on=\"A & B\"",
            "rule \"and_left\" on=\"A & B\" formula=\"A & B -> C\"",
            "rule \"and_left\" on=\"A & B\" formula=\"A & B -> C\" occ=1",
            "rule \"and_left\" on=\"A & B\" formula=\"A & B -> C\" occ=1 inst_A=\"true\" inst_B=\"false\""
        })
    public static class Parameters {
        @Option(value = "#2", help = "The name of the rule to be applied.")
        public String rulename;
        @Option(value = "on", required = false, help = "The term to be used as the \"find\" term in a taclet with \"find\". (Matching artifacts are supported)")
        public Term on;
        @Option(value = "formula", required = false)
        public Term formula;
        @Option(value = "occ", required = false, help = "The number of the occurrence of 'on' in case there are several applicable rule apps.")
        public int occ = -1;
        /**
         * Represents a part of a formula (may use Java regular expressions as
         * long as supported by proof script parser). Rule is applied to the
         * sequent formula which matches that string.
         */
        @Option(value = "matches", required = false, help = "Instead of giving the toplevel formula completely, a regular expression can be specified to match the toplevel formula as a string.")
        public String matches = null;
        @Option(value = "assumes", required = false, help = "The assumptions that must be satisfied for the rule to be applied.")
        public Sequent assumes = null;
        @Varargs(as = String.class, prefix = "inst_")
        public Map<String, String> instantiations = new HashMap<>();
    }

    private static class TacletNameFilter extends TacletFilter {
        private final Name rulename;

        public TacletNameFilter(String rulename) {
            this.rulename = new Name(rulename);
        }

        @Override
        protected boolean filter(Taclet taclet) {
            return taclet.name().equals(rulename);
        }
    }

}
