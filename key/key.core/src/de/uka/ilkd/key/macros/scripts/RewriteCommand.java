package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
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
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Debug;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * rewrite find="t1" replace="t2"; (mulbrich script syntax)
 * rewrite find=`t1` replace=`t2`; (psdbg)
 */
public class RewriteCommand extends AbstractCommand<RewriteCommand.Parameters>{
    public RewriteCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "rewrite";
    }


    @Override public Parameters evaluateArguments(EngineState state,
                                                              Map<String, String> arguments) throws Exception {
        Parameters p = state.getValueInjector()
                .inject(this, new Parameters(), arguments);
        return p;
    }

    @Override public void execute(AbstractUserInterfaceControl uiControl,
                                  Parameters args, EngineState state)
            throws ScriptException, InterruptedException {
        Proof proof = state.getProof();
        assert proof != null;

        //get all Taclets
        ImmutableList<TacletApp> allApps = findAllTacletApps(args, state);

        //filter only taclets on find, also sets allReplSucc to false if one replacement isn't successful
        //TODO: failPosInOcc only needed for different cut structures
        List<PosInOccurrence> failposInOccs = findAndExecReplacement(args, allApps, state);

        if (failposInOccs.size() >= 1) {

            System.out.println("Cut needed");
           CutCommand cut = new CutCommand();
           CutCommand.Parameters param = new CutCommand.Parameters();
           param.formula = args.replace;

           cut.execute(uiControl, param, state);
           System.out.println("After final cut:"+ state.getFirstOpenGoal().sequent());


        }

    }

    public static class Parameters {
        @Option(value = "find", required = true)
        public Term find;
        @Option(value = "replace", required = true)
        public Term replace;
        @Option(value = "formula", required = false)
        public Term formula;
    }

    /**
     * get aLl TacletApps
     */
    private ImmutableList<TacletApp> findAllTacletApps(Parameters p,
                                                       EngineState state) throws ScriptException {
        Services services = state.getProof().getServices();
        TacletFilter filter = TacletFilter.TRUE;
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

 /**
 * Filter tacletapps: term = find && result = replace
 **/
 //TODO: probably void, except if we want the failed PosInOccs
    private List<PosInOccurrence> findAndExecReplacement(Parameters p,
                                       ImmutableList<TacletApp> list, EngineState state) {
        //List of PosInOcc that haven't been  succ replaced
        List<PosInOccurrence> failposInOccs = new ArrayList<PosInOccurrence>();
        System.out.println("Size = 0:" + failposInOccs.size());

        //List of PosInOcc that succ replaced
        List<PosInOccurrence> succposInOccs = new ArrayList<PosInOccurrence>();

        for (TacletApp tacletApp : list) {
            if (tacletApp instanceof PosTacletApp) {


                PosTacletApp pta = (PosTacletApp) tacletApp;


                if (pta.posInOccurrence().subTerm()
                        .equals(p.find)) {
                    System.out.println("________________________________________");
                    System.out.println("Tacletapp an der Stelle: " + tacletApp.posInOccurrence());
                    System.out.println("Tacletname an der Stelle: " + pta.taclet().displayName());
                    //if Term already succ replaced, the skip
                    if(succposInOccs.contains(pta.posInOccurrence())) {
                        System.out.println("Term already successfully replaced.");
                        continue;
                    }

                    // TODO: if taclet transforms find to replace then execute and add to list, else null

                    try {
                        System.out.println("Term NOT already successfully replaced.");

                        Goal goalold = state.getFirstOpenGoal();
                        System.out.println("Goal: " + goalold.sequent());

                        Goal goal = goalold;
                        goal.apply(tacletApp);
                        //state.setGoal((Goal) null);

                        //TODO: nicht immer an der gleichen pio
                        if (pta.posInOccurrence().subTerm()
                                .equals(p.replace)) {

                            failposInOccs.remove(pta.posInOccurrence());
                            succposInOccs.add(pta.posInOccurrence());
                            System.out.println("Sucessful Replacement");
                        } else {
                            if (!failposInOccs.contains(pta.posInOccurrence())) {
                                System.out.println("Unsucessful Replacement & add to failed list:");
                                failposInOccs.add(pta.posInOccurrence());
                                state.setGoal(goalold);
                            } else {
                                //prune
                                System.out.println("Unsucessful Replacement & already in failed list");
                                state.setGoal(goalold);
                            }
                        }
                    } catch (Exception e) {
                        if(!failposInOccs.contains(pta.posInOccurrence())) {
                            failposInOccs.add(pta.posInOccurrence());
                        }
                        System.out.println("TacletApp not applicable");
                        e.printStackTrace();
                        continue;
                    }


                }
            }
        }
        System.out.println("[End of findExec] Size = ? :" + failposInOccs.size());
        return failposInOccs;
    }



}

