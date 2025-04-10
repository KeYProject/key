/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

public class RuleApplication {

    private static final int TIME_OUT = -1;
    private static final int MAX_RULE_APP = 40000;
    private final Sequent seq;
    final Services services;
    private ProofStarter ps;
    private Proof proof;

    public RuleApplication(Services s, Sequent sequent) {
        seq = sequent;
        final ProofEnvironment env =
            SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(s.getProof());
        ps = new ProofStarter(false);
        try {
            ps.init(seq, env, "LoopInv");
        } catch (ProofInputException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        final StrategyProperties sp =
            ps.getProof().getActiveStrategyFactory().getSettingsDefinition()
                    .getDefaultPropertiesFactory().createDefaultStrategyProperties();
        sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_OFF);
        sp.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_NONE);
        sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_EXPAND);
        sp.setProperty(StrategyProperties.MPS_OPTIONS_KEY, StrategyProperties.MPS_MERGE);

        ps.setStrategyProperties(sp);
        ps.getProof().getSettings().getStrategySettings().setActiveStrategyProperties(sp);
        ps.getProof().getSettings().getStrategySettings().setMaxSteps(MAX_RULE_APP);
        ps.getProof().getEnv().getInitConfigForEnvironment().getSettings().getStrategySettings()
                .setMaxSteps(MAX_RULE_APP);
        ps.getProof().getSettings().getStrategySettings().setTimeout(TIME_OUT);
        ps.getProof().getEnv().getInitConfigForEnvironment().getSettings().getStrategySettings()
                .setTimeout(TIME_OUT);

        ps.setMaxRuleApplications(MAX_RULE_APP);// Only Change This
        ps.setTimeout(TIME_OUT);

        proof = ps.getProof();
        services = proof.getServices();
    }


    ///////////////////////////////////// Nested Loop
    ///////////////////////////////////// Usecase///////////////////////////////////////////

    ImmutableList<Goal> applyNestedLoopUsecaseRule(ImmutableList<Goal> openGoals) {
        Goal currentGoal = findNestedLoopUsecaseTacletGoal(openGoals);

        if (currentGoal == null) {
            // System.out.println("OPEN GOAL: " + openGoals);
            throw new IllegalStateException("Goal for applying NestedLoopUsecase rule is null.");

        }

        IBuiltInRuleApp app = null;
        for (SequentFormula sf : currentGoal.sequent().succedent()) {
            app =
                findNestedLoopUsecaseRuleApp(currentGoal.ruleAppIndex().getBuiltInRules(currentGoal,
                    new PosInOccurrence(sf, PosInTerm.getTopLevel(), false)));
            if (app != null) {
                break;
            }
        }
        if (app != null) {
            Node subtreeRoot = currentGoal.node();

            final ImmutableList<Goal> goals = currentGoal.apply(app);

            // System.out.println("Number of Open Goals after applying NestedLoopUsecase: " +
            // currentGoal.proof().openGoals().size());
            // System.out.println("After NestedLoopUsecase:" +
            // ProofSaver.printAnything(currentGoal.sequent(), services));
            // try {
            ////// System.out.println("Number of Open Goals after simplification: " +
            // ps.getProof().openGoals().size() + "+++" + (ps.getProof() == currentGoal.proof()));
            ////
            // new ProofSaver(ps.getProof(), new
            // File("C:\\Users\\Asma\\NestedLoopUsecaseRuleApplication.key")).save();
            // } catch (IOException e) {
            // e.printStackTrace();
            // }
            ApplyStrategyInfo info = ps.start(goals);
            // System.out.println("Info" + info);
            for (Goal g : ps.getProof().getSubtreeGoals(subtreeRoot)) {
                // System.out.println("After Start:"+g.sequent());
            }
            // try {
            ////// System.out.println("Number of Open Goals after simplification: " +
            // ps.getProof().openGoals().size() + "+++" + (ps.getProof() == currentGoal.proof()));
            ////
            // new ProofSaver(ps.getProof(), new
            // File("C:\\Users\\Asma\\AfterSymExeOfNestedLoopUsecaseRuleApplication.key")).save();
            // } catch (IOException e) {
            //// // TODO Auto-generated catch block
            // e.printStackTrace();
            // }
            return ps.getProof().getSubtreeGoals(subtreeRoot);
            // return currentGoal.proof().openGoals();
            // return services.getProof().openEnabledGoals();
        }
        return null;
    }

    Goal findNestedLoopUsecaseTacletGoal(ImmutableList<Goal> goals) {
        for (Goal g : goals) {
            for (SequentFormula sf : g.sequent().succedent()) {
                IBuiltInRuleApp bApp = findNestedLoopUsecaseRuleApp(
                    g.ruleAppIndex().getBuiltInRules(g,
                        new PosInOccurrence(sf, PosInTerm.getTopLevel(), false)));
                if (bApp != null) {
                    // System.out.println("Goal of taclet NestedLoopUsecase is: " + g.sequent());
                    return g;
                }
            }
            // System.out.println("Taclet NestedLoopUsecase" + " is not applicable at " + g);
        }
        return null;
    }

    private IBuiltInRuleApp findNestedLoopUsecaseRuleApp(ImmutableList<IBuiltInRuleApp> tApp) {
        for (IBuiltInRuleApp app : tApp) {
            if (NestedLoopUsecaseRule.NESTED_LOOP_USECASE_RUlE_NAME.equals(app.rule().name())) {
                // System.out.println(NestedLoopUsecaseRule.NESTED_LOOP_USECASE_RUlE_NAME + " is
                // among applicable rules.");
                return app;
            }
        }
        return null;
    }

    ///////////////////////////////////// Shift Update///////////////////////////////////////////

    ImmutableList<Goal> applyShiftUpdateRule(ImmutableList<Goal> openGoals) {
        Goal currentGoal = findShiftUpdateTacletGoal(openGoals);

        if (currentGoal == null) {
            System.out.println("No shift possible. OPEN GOAL: " + openGoals);
            // throw new IllegalStateException("Goal for applying Shift rule is null.");
            return openGoals;
        }

        IBuiltInRuleApp app = null;
        for (SequentFormula sf : currentGoal.sequent().succedent()) {
            app = findShiftUpdateRuleApp(currentGoal.ruleAppIndex().getBuiltInRules(currentGoal,
                new PosInOccurrence(sf, PosInTerm.getTopLevel(), false)));
            if (app != null) {
                break;
            }
        }
        if (app != null) {
            Node subtreeRoot = currentGoal.node();

            final ImmutableList<Goal> goals = currentGoal.apply(app);

            // try {
            // new ProofSaver(ps.getProof(), new
            // File("C:\\Users\\Asma\\afterShiftUpdate.key")).save();
            // } catch (IOException e) {
            // e.printStackTrace();
            // }

            ApplyStrategyInfo info = ps.start(goals);

            ImmutableList<Goal> subtreeGoals = ps.getProof().getSubtreeGoals(subtreeRoot);

            //System.out.println("info after shift: "+info + ":" + subtreeGoals);


            return subtreeGoals;

        }
        return openGoals;
    }

    Goal findShiftUpdateTacletGoal(ImmutableList<Goal> goals) {
        for (Goal g : goals) {
            for (SequentFormula sf : g.sequent().succedent()) {
                IBuiltInRuleApp bApp = findShiftUpdateRuleApp(
                    g.ruleAppIndex().getBuiltInRules(g,
                        new PosInOccurrence(sf, PosInTerm.getTopLevel(), false)));
                if (bApp != null) {
                    // System.out.println("Goal of taclet shiftUpdate" + " is: " + g);
                    return g;
                }
            }
            System.out.println("Taclet shiftUpdate" + " is not applicable at " + g);
        }
        return null;
    }

    private IBuiltInRuleApp findShiftUpdateRuleApp(ImmutableList<IBuiltInRuleApp> tApp) {
        for (IBuiltInRuleApp app : tApp) {
            if (ShiftUpdateRule.SHIFT_UPDATE_NAME.equals(app.rule().name())) {
                // System.out.println(ShiftUpdateRule.SHIFT_UPDATE_NAME + " rule is among applicable
                // rules.");
                return app;
            }
        }
        return null;
    }


    ///////////////////////////////////// Loop Unwind///////////////////////////////////////////

    ImmutableList<Goal> applyUnwindRule(ImmutableList<Goal> openGoals) {
        ImmutableList<TacletApp> tApp = ImmutableSLList.<TacletApp>nil();
        Goal currentGoal = findLoopUnwindTacletGoal(openGoals);
        if (currentGoal == null) {
            throw new IllegalStateException("Goal is null.");
        }

        for (SequentFormula sf : currentGoal.sequent().succedent()) {
            tApp = findLoopUnwindTaclet(sf, currentGoal);
            if (!tApp.isEmpty()) {
                break;
            }
        }
        if (!tApp.isEmpty()) {
            assert tApp.size() == 1;
            TacletApp app = tApp.head();
            app = app.tryToInstantiate(services);
            ImmutableList<Goal> goals = currentGoal.apply(app);

            // try {
            // new ProofSaver(ps.getProof(), new
            // File("C:\\Users\\Asma\\afterLoopUnwind.key")).save();
            // } catch (IOException e) {
            // e.printStackTrace();
            // }

            // ApplyStrategyInfo info =
            ps.start(goals);
            // System.out.println("info after unwind: "+ currentGoal.proof().openGoals().head());

            // try {
            // new ProofSaver(ps.getProof(), new
            // File("C:\\Users\\Asma\\afterLoopUnwind.key")).save();
            // } catch (IOException e) {
            // e.printStackTrace();
            // }

            return currentGoal.proof().openGoals();
        }
        return null;
    }

    Goal findLoopUnwindTacletGoal(ImmutableList<Goal> goals) {
        for (Goal g : goals) {
            for (SequentFormula sf : g.sequent().succedent()) {
                ImmutableList<TacletApp> tApp = findLoopUnwindTaclet(sf, g);
                if (!tApp.isEmpty()) {
                    return g;
                }
            }
            System.out.println("Taclet loopUnwind is not applicable at " + g);
        }
        return null;
    }

    private ImmutableList<TacletApp> findLoopUnwindTaclet(SequentFormula sf, Goal g) {
        ImmutableList<TacletApp> tApp = g.ruleAppIndex().getTacletAppAtAndBelow(new TacletFilter() {
            @Override
            protected boolean filter(Taclet taclet) {
                return taclet.name().toString().equals("loopUnwind");
            }
        }, new PosInOccurrence(sf, PosInTerm.getTopLevel(), false), services);

        return tApp;
    }

    ///////////////////////////////////// LoopScope Loop
    ///////////////////////////////////// Unwind///////////////////////////////////////////

    ImmutableList<Goal> applyLoopScopeUnwindRule(ImmutableList<Goal> openGoals) {
        ImmutableList<TacletApp> tApp = ImmutableSLList.<TacletApp>nil();
        Goal currentGoal = findLoopUnwindTacletGoal(openGoals);
        if (currentGoal == null) {
            throw new IllegalStateException("Goal is null.");
        }

        for (SequentFormula sf : currentGoal.sequent().succedent()) {
            tApp = findLoopScopeLoopUnwindTaclet(sf, currentGoal);
            if (!tApp.isEmpty()) {
                break;
            }
        }
        if (!tApp.isEmpty()) {
            assert tApp.size() == 1;
            TacletApp app = tApp.head();
            app = app.tryToInstantiate(services);
            ImmutableList<Goal> goals = currentGoal.apply(app);

            // try {
            // new ProofSaver(ps.getProof(), new
            // File("C:\\Users\\Asma\\afterLoopScopeLoopUnwind.key")).save();
            // } catch (IOException e) {
            // e.printStackTrace();
            // }

            // ApplyStrategyInfo info =
            ps.start(goals);
            // System.out.println("info after unwind: "+info);

            return currentGoal.proof().openGoals();
        }
        return null;
    }

    LoopStatement getLoopStatementFromGoal(Goal g) {
        for (SequentFormula sf : g.sequent().succedent()) {
            ImmutableList<TacletApp> tApp = findLoopScopeLoopUnwindTaclet(sf, g);
            if (!tApp.isEmpty()) {
                return (LoopStatement) JavaTools.getActiveStatement(sf.formula().javaBlock());
            }
        }
        return null;
    }

    Goal findLoopScopeLoopUnwindTacletGoal(ImmutableList<Goal> goals) {
        for (Goal g : goals) {
            for (SequentFormula sf : g.sequent().succedent()) {
                ImmutableList<TacletApp> tApp = findLoopScopeLoopUnwindTaclet(sf, g);
                if (!tApp.isEmpty()) {
                    return g;
                }
            }
            System.out.println("Taclet unwindLoopScope is not applicable at " + g);
        }
        return null;
    }

    private ImmutableList<TacletApp> findLoopScopeLoopUnwindTaclet(SequentFormula sf, Goal g) {
        ImmutableList<TacletApp> tApp = g.ruleAppIndex().getTacletAppAtAndBelow(new TacletFilter() {
            @Override
            protected boolean filter(Taclet taclet) {
                return taclet.name().toString().equals("unwindLoopScope");
            }
        }, new PosInOccurrence(sf, PosInTerm.getTopLevel(), false), services);

        return tApp;
    }
}
