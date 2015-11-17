package de.uka.ilkd.key.macros.scripts;

import java.util.ArrayList;
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
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

public class RuleCommand extends AbstractCommand {

    @Override
    public String getName() {
        return "rule";
    }

    private static class Parameters {
        String rulename;
        Term on;
        Term formula;
        int occ = -1;
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

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof,
            Map<String, String> args, Map<String, Object> state) throws ScriptException, InterruptedException {

        Parameters p = parseArgs(proof, args, state);
        TacletApp theApp = makeTacletApp(proof, p, state);
        assert theApp != null;

        ImmutableList<TacletApp> assumesCandidates =
                theApp.findIfFormulaInstantiations(getFirstOpenGoal(proof, state).sequent(), proof.getServices());

        if(assumesCandidates.size() != 1) {
            throw new ScriptException("Not a unique \\assumes instantiation");
        }

        theApp = assumesCandidates.head();

        // instantiate remaining symbols
        theApp = theApp.tryToInstantiate(proof.getServices());

        if(theApp == null) {
            throw new ScriptException("Cannot instantiate this rule");
        }

        Goal g = getFirstOpenGoal(proof, state);
        g.apply(theApp);
    }

    private TacletApp makeTacletApp(Proof proof, Parameters p,
            Map<String, Object> state) throws ScriptException {

        Taclet taclet = proof.getEnv().getInitConfigForEnvironment().
                lookupActiveTaclet(new Name(p.rulename));

        if(taclet == null) {
            throw new ScriptException("Taclet '" + p.rulename + "' not known.");
        }

        if(taclet instanceof NoFindTaclet) {
            return makeNoFindTacletApp(taclet, proof, p, state);
        } else {
            return findTacletApp(proof, p, state);
        }

    }

    private TacletApp makeNoFindTacletApp(Taclet taclet, Proof proof, Parameters p,
            Map<String, Object> state) {

        TacletApp app = NoPosTacletApp.createNoPosTacletApp(taclet);

        // TODO allow for sv instantiations at this point
//        SchemaVariable sv = app.uninstantiatedVars().iterator().next();
        // app = app.addCheckedInstantiation(sv, formula, proof.getServices(), true);

        return app;
    }

    private TacletApp findTacletApp(Proof proof, Parameters p, Map<String, Object> state)
            throws ScriptException {

        ImmutableList<TacletApp> allApps = findAllTacletApps(proof, p, state);
        List<TacletApp> matchingApps = filterList(p, allApps);

        if(matchingApps.isEmpty()) {
            throw new ScriptException("No matching applications.");
        }

        if(p.occ < 0) {
            if(matchingApps.size() > 1)  {
                throw new ScriptException("More than one applicable occurrence");
            }
            return matchingApps.get(0);
        } else {
            if(p.occ >= matchingApps.size()) {
                throw new ScriptException("Occurence " + p.occ
                        + " has been specified, but there only "
                        + matchingApps.size() + " hits.");
            }
            return matchingApps.get(p.occ);
        }
    }

    private ImmutableList<TacletApp> findAllTacletApps(Proof proof, Parameters p, Map<String, Object> state)
            throws ScriptException {
        Services services = proof.getServices();
        TacletFilter filter = new TacletNameFilter(p.rulename);
        Goal g = getFirstOpenGoal(proof, state);
        RuleAppIndex index = g.ruleAppIndex ();
        index.autoModeStopped ();

        ImmutableList<TacletApp> allApps = ImmutableSLList.nil();
        for (SequentFormula sf : g.node().sequent().antecedent()) {
            if(p.formula != null && !sf.formula().equalsModRenaming(p.formula)) {
                continue;
            }
            allApps = allApps.append(
                    index.getTacletAppAtAndBelow(filter,
                            new PosInOccurrence(sf, PosInTerm.getTopLevel(), true),
                            services));
        }

        for (SequentFormula sf : g.node().sequent().succedent()) {
            if(p.formula != null && !sf.formula().equalsModRenaming(p.formula)) {
                continue;
            }
            allApps = allApps.append(
                    index.getTacletAppAtAndBelow(filter,
                            new PosInOccurrence(sf, PosInTerm.getTopLevel(), false),
                            services));
        }

        return allApps;
    }
    /*
     * Filter those apps from a list that are according to the parameters.
     */
    private List<TacletApp> filterList(Parameters p, ImmutableList<TacletApp> list) {
        List<TacletApp> matchingApps = new ArrayList<TacletApp>();
        for (TacletApp tacletApp : list) {
            if(tacletApp instanceof PosTacletApp) {
                PosTacletApp pta = (PosTacletApp) tacletApp;
                if(p.on == null || pta.posInOccurrence().subTerm().equals(p.on)) {
                    matchingApps.add(pta);
                }
            }
        }
        return matchingApps;
    }

    private static Parameters parseArgs(Proof proof, Map<String, String> args, Map<String, Object> state)
            throws ScriptException {

        Parameters result = new Parameters();

        result.rulename = args.get("#2");
        if(result.rulename == null) {
            throw new ScriptException("Rule name must be set");
        }

        try {
            //
            // on="term to apply to as find"
            String onStr = args.get("on");
            if(onStr != null) {
                result.on = toTerm(proof, state, onStr, null);
            }

            //
            // formula="toplevel formula in which it appears"
            String formStr = args.get("formula");
            if(formStr != null) {
                result.formula = toTerm(proof, state, formStr, null);
            }

            //
            // occurrence number;
            String occStr = args.get("occ");
            if(occStr != null) {
                result.occ = Integer.parseInt(occStr);
            }
        } catch(Exception e) {
            throw new ScriptException(e);
        }

        return result;
    }
}
