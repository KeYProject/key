package de.uka.ilkd.key.macros.scripts;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.Varargs;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Command that applies a calculus rule
 * All parameters are passed as strings and converted by the command.
 * The parameters are:
 * <ol>
 *     <li>#2 = <String>rule name</String></li>
 *     <li>on= key.core.logic.Term on which the rule should be applied to as String (find part of the rule) </li>
 *     <li>formula= toplevel formula in which term appears in</li>
 *     <li>occ = occurrence number</li>
 *     <li>inst_= instantiation</li>
 * </ol>
 */
public class RuleCommand extends AbstractCommand<RuleCommand.Parameters> {

    public RuleCommand() {
        super(Parameters.class);
    }

    @Override public String getName() {
        return "rule";
    }

    @Override public Parameters evaluateArguments(EngineState state,
            Map<String, String> arguments) throws Exception {
        Parameters p = state.getValueInjector()
                .inject(this, new Parameters(), arguments);

        // instantiation
        /*
        arguments.forEach((String s, String value) -> {
            if (s.startsWith("inst_")) {
                s = s.substring(5);
            }

            try {
                p.instantiations.put(s, state.toTerm(value, null));
            }
            catch (ParserException | ScriptException e) {
                e.printStackTrace();
            }
        });
        */
        return p;
    }

    @Override public void execute(AbstractUserInterfaceControl uiControl,
            Parameters args, EngineState state)
            throws ScriptException, InterruptedException {
        Proof proof = state.getProof();
        TacletApp theApp = makeTacletApp(args, state);
        assert theApp != null;

        ImmutableList<TacletApp> assumesCandidates = theApp
                .findIfFormulaInstantiations(
                        state.getFirstOpenGoal().sequent(),
                        proof.getServices());

        if (assumesCandidates.size() != 1) {
            throw new ScriptException("Not a unique \\assumes instantiation");
        }

        theApp = assumesCandidates.head();

        {
            /*
             * (DS, 2019-01-31): Try to instantiate first, otherwise, we cannot
             * apply taclets with "\newPV", Skolem terms etc.
             */
            final TacletApp maybeInstApp = theApp
                    .tryToInstantiate(proof.getServices().getOverlay(
                            state.getFirstOpenGoal().getLocalNamespaces()));

            if (maybeInstApp != null) {
                theApp = maybeInstApp;
            }
        }

        for (SchemaVariable sv : theApp.uninstantiatedVars()) {
            if (theApp.isInstantiationRequired(sv)) {
                Term inst = args.instantiations.get(sv.name().toString());
                if (inst == null) {
                    throw new ScriptException(
                            "missing instantiation for " + sv);
                }
                theApp = theApp
                        .addInstantiation(sv, inst, true, proof.getServices());
            }
        }

        // try to instantiate remaining symbols
        theApp = theApp.tryToInstantiate(proof.getServices().getOverlay(state.getFirstOpenGoal().getLocalNamespaces()));

        if (theApp == null) {
            throw new ScriptException("Cannot instantiate this rule");
        }

        Goal g = state.getFirstOpenGoal();
        g.apply(theApp);
        state.setGoal((Goal) null);
    }

    private TacletApp makeTacletApp(Parameters p, EngineState state)
            throws ScriptException {

        Proof proof = state.getProof();
        Taclet taclet = proof.getEnv().getInitConfigForEnvironment().
                lookupActiveTaclet(new Name(p.rulename));

        if (taclet == null) {
            throw new ScriptException("Taclet '" + p.rulename + "' not known.");
        }

        if (taclet instanceof NoFindTaclet) {
            return makeNoFindTacletApp(taclet);
        }
        else {
            return findTacletApp(p, state);
        }

    }

    private TacletApp makeNoFindTacletApp(Taclet taclet/*, Parameters p,
            EngineState state*/) {
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(taclet);
        return app;
    }

    private TacletApp findTacletApp(Parameters p, EngineState state)
            throws ScriptException {

        ImmutableList<TacletApp> allApps = findAllTacletApps(p, state);
        List<TacletApp> matchingApps = filterList(p, allApps);

        if (matchingApps.isEmpty()) {
            throw new ScriptException("No matching applications.");
        }

        if (p.occ < 0) {
            if (matchingApps.size() > 1) {
                throw new ScriptException(
                        "More than one applicable occurrence");
            }
            return matchingApps.get(0);
        }
        else {
            if (p.occ >= matchingApps.size()) {
                throw new ScriptException("Occurence " + p.occ
                        + " has been specified, but there are only "
                        + matchingApps.size() + " hits.");
            }
            return matchingApps.get(p.occ);
        }
    }

    private ImmutableList<TacletApp> findAllTacletApps(Parameters p,
            EngineState state) throws ScriptException {
        Services services = state.getProof().getServices();
        TacletFilter filter = new TacletNameFilter(p.rulename);
        Goal g = state.getFirstOpenGoal();
        RuleAppIndex index = g.ruleAppIndex();
        index.autoModeStopped();

        ImmutableList<TacletApp> allApps = ImmutableSLList.nil();
        for (SequentFormula sf : g.node().sequent().antecedent()) {
            if (p.formula != null && !sf.formula()
                    .equalsModRenaming(p.formula)) {
                continue;
            }
            allApps = allApps.append(index.getTacletAppAtAndBelow(filter,
                    new PosInOccurrence(sf, PosInTerm.getTopLevel(), true),
                    services));
        }

        for (SequentFormula sf : g.node().sequent().succedent()) {
            if (p.formula != null && !sf.formula()
                    .equalsModRenaming(p.formula)) {
                continue;
            }
            allApps = allApps.append(index.getTacletAppAtAndBelow(filter,
                    new PosInOccurrence(sf, PosInTerm.getTopLevel(), false),
                    services));
        }

        return allApps;
    }

    /*
     * Filter those apps from a list that are according to the parameters.
     */
    private List<TacletApp> filterList(Parameters p,
            ImmutableList<TacletApp> list) {
        List<TacletApp> matchingApps = new ArrayList<TacletApp>();
        for (TacletApp tacletApp : list) {
            if (tacletApp instanceof PosTacletApp) {
                PosTacletApp pta = (PosTacletApp) tacletApp;
                if (p.on == null || pta.posInOccurrence().subTerm()
                        .equalsModRenaming(p.on)) {
                    matchingApps.add(pta);
                }
            }
        }
        return matchingApps;
    }

    public static class Parameters {
        @Option(value = "#2")
        public String rulename;
        @Option(value = "on", required = false)
        public Term on;
        @Option(value = "formula", required = false)
        public Term formula;
        @Option(value = "occ", required = false)
        public int occ = -1;
        @Varargs(as = Term.class, prefix = "inst_")
        public Map<String, Term> instantiations = new HashMap<>();
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

    /*
    private static Parameters parseArgs(
            Map<String, String> args,
            EngineState state) throws ScriptException {

        Parameters result = new Parameters();

        try {
            for (Entry<String, String> arg : args.entrySet()) {
                switch (arg.getKey()) {
                case "#2":
                    // rule name
                    result.rulename = args.get("#2");
                    break;
                case "on":
                    // on="term to apply to as find"
                    result.on = state.toTerm(proof, state, arg.getValue(), null);
                    break;
                case "formula":
                    // formula="toplevel formula in which it appears"
                    result.formula = state.toTerm(proof, state, arg.getValue(), null);
                    break;
                case "occ":
                    // occurrence number;
                    result.occ = Integer.parseInt(arg.getValue());
                    break;
                default:
                    // instantiation
                    String s = arg.getKey();
                    if (!s.startsWith("#")) {
                        if (s.startsWith("inst_")) {
                            s = s.substring(5);
                        }
                        result.instantiations.put(s,
                                toTerm(proof, state, arg.getValue(), null));
                    }
                }
            }
        }
        catch (Exception e) {
            throw new ScriptException(e);
        }

        if (result.rulename == null) {
            throw new ScriptException("Rule name must be set");
        }

        return result;
    }*/
}
