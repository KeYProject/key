// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.ui;

import java.io.File;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.gui.ApplyTacletDialogModel;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.SkipMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader.ReplayResult;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.SingleThreadProblemLoader;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentEvent;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Debug;

public abstract class AbstractUserInterface implements UserInterface {

    private ProofMacro autoMacro = new SkipMacro();
    protected boolean saveOnly = false;

    private ProverTaskListener pml = null;

    private int numOfInvokedMacros = 0;
    
    private boolean minimizeInteraction; // minimize user interaction

    @Override
    public  IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced) {
        app = forced? app.forceInstantiate(goal): app.tryToInstantiate(goal);
        // cannot complete that app
        return app.complete() ? app : null;
    }

    public void setSaveOnly(boolean s) {
        this.saveOnly = s;
    }
    
    public boolean isSaveOnly() {
        return this.saveOnly;
    }

    public void setMacro(ProofMacro macro) {
        assert macro != null;
        this.autoMacro = macro;
    }

    public ProofMacro getMacro() {
        return this.autoMacro;
    }

    public boolean macroChosen() {
        return !(getMacro() instanceof SkipMacro);
    }

    @Override
    public final ProverTaskListener getListener() {
        if (this.pml == null) {
            this.pml = new ProofMacroListenerAdapter();
        }
        return new CompositePTListener(this, pml);
    }

   /**
     * {@inheritDoc}
     */
    @Override
    public Proof createProof(InitConfig initConfig, ProofOblInput input) throws ProofInputException {
       ProblemInitializer init = createProblemInitializer(initConfig.getProfile());
       ProofAggregate proofList = init.startProver(initConfig, input);
       createProofEnvironmentAndRegisterProof(input, proofList, initConfig);
       return proofList.getFirstProof();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void proofCreated(ProblemInitializer sender, ProofAggregate proofAggregate) {
       // Nothing to do
    }

    @Override
    public void proofUnregistered(ProofEnvironmentEvent event) {
       if (event.getSource().getProofs().isEmpty()) {
          event.getSource().removeProofEnvironmentListener(this);
       }
    }
    
    public boolean isAtLeastOneMacroRunning() {
       return numOfInvokedMacros != 0;
    }

    protected void macroStarted(String message, int size) {
        numOfInvokedMacros++;
    }

    protected void macroFinished(ProofMacroFinishedInfo info) {
        numOfInvokedMacros--;
    }

    private class ProofMacroListenerAdapter implements ProverTaskListener {

        @Override
        public void taskStarted(String message, int size) {
            macroStarted(message, size);
        }

        @Override
        public void taskProgress(int position) {
            // not needed yet
        }

        @Override
        public void taskFinished(TaskFinishedInfo info) {
            if (info instanceof ProofMacroFinishedInfo) {
               macroFinished((ProofMacroFinishedInfo)info);
            }
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isAutoModeSupported(Proof proof) {
       return proof != null && !proof.isDisposed(); // All not disposed proofs are supported.
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractProblemLoader load(Profile profile,
                                     File file,
                                     List<File> classPath,
                                     File bootClassPath,
                                     Properties poPropertiesToForce,
                                     boolean forceNewProfileOfNewProofs) throws ProblemLoaderException {
       AbstractProblemLoader loader = null;
       try {
          loader = new SingleThreadProblemLoader(file, classPath, bootClassPath, profile, forceNewProfileOfNewProofs,
                                                 this, false, poPropertiesToForce);
          loader.load();
          return loader;
       }
       catch(ProblemLoaderException e) {
           if (loader != null && loader.getProof() != null) {
               loader.getProof().dispose();
           }
           // rethrow that exception
           throw e;
       }
       catch (Throwable e) {
           if (loader != null && loader.getProof() != null) {
               loader.getProof().dispose();
           }
           throw new ProblemLoaderException(loader, e);
       }
    }

    @Override
    public ProblemInitializer createProblemInitializer(Profile profile) {
        ProblemInitializer pi = new ProblemInitializer(this, new Services(profile), this);
        return pi;
    }

    @Override
    public void loadingStarted() {
    }

    @Override
    public void loadingFinished(AbstractProblemLoader loader, LoadedPOContainer poContainer, ProofAggregate proofList, ReplayResult result) throws ProblemLoaderException {
       if (proofList != null) {
          // avoid double registration at spec repos as that is done already earlier in createProof
          // the UI method should just do the necessarily UI registrations
          createProofEnvironmentAndRegisterProof(poContainer.getProofOblInput(), proofList, loader.getInitConfig());
       }
    }
    
    @Override
    public boolean isMinimizeInteraction() {
       return minimizeInteraction;
    }

    @Override
    public void setMinimizeInteraction(boolean minimizeInteraction) {
       this.minimizeInteraction = minimizeInteraction;
    }
    
    
    
    
    
    
    
    
    
    
    
    
    


    @Override
   public ImmutableList<BuiltInRule> getBuiltInRule(Goal focusedGoal, PosInOccurrence pos) {
        ImmutableList<BuiltInRule> rules = ImmutableSLList.<BuiltInRule>nil();

        for (RuleApp ruleApp : focusedGoal.ruleAppIndex().getBuiltInRules(focusedGoal, pos)) {
            BuiltInRule r = (BuiltInRule) ruleApp.rule();
            if (!rules.contains(r)) {
                rules = rules.prepend(r);
            }
        }
        return rules;
    }
    


    @Override
   public ImmutableList<TacletApp> getNoFindTaclet(Goal focusedGoal) {
        return filterTaclet(focusedGoal, focusedGoal.ruleAppIndex().
                getNoFindTaclet(TacletFilter.TRUE,
                      focusedGoal.proof().getServices()), null);
    }

    @Override
   public ImmutableList<TacletApp> getFindTaclet(Goal focusedGoal, PosInOccurrence pos) {
        if (pos != null && pos != null && focusedGoal != null) {
            Debug.out("NoPosTacletApp: Looking for applicables rule at node",
                    focusedGoal.node().serialNr());
            return filterTaclet(focusedGoal, focusedGoal.ruleAppIndex().
                    getFindTaclet(TacletFilter.TRUE,
                            pos,
                            focusedGoal.proof().getServices()), pos);
        }
        return ImmutableSLList.<TacletApp>nil();
    }

    @Override
   public ImmutableList<TacletApp> getRewriteTaclet(Goal focusedGoal, PosInOccurrence pos) {
        if (pos != null) {
            return filterTaclet(focusedGoal, focusedGoal.ruleAppIndex().
                    getRewriteTaclet(TacletFilter.TRUE,
                            pos,
                            focusedGoal.proof().getServices()), pos);
        }

        return ImmutableSLList.<TacletApp>nil();
    }

    /**
     * takes NoPosTacletApps as arguments and returns a duplicate free list of
     * the contained TacletApps
     */
    private ImmutableList<TacletApp> filterTaclet(Goal focusedGoal, ImmutableList<NoPosTacletApp> tacletInstances, PosInOccurrence pos) {
        java.util.HashSet<Taclet> applicableRules = new java.util.HashSet<Taclet>();
        ImmutableList<TacletApp> result = ImmutableSLList.<TacletApp>nil();
        for (NoPosTacletApp app : tacletInstances) {
            if (isMinimizeInteraction()) {
                ImmutableList<TacletApp> ifCandidates
                        = app.findIfFormulaInstantiations(
                              focusedGoal.sequent(),
                              focusedGoal.proof().getServices());
                if (ifCandidates.isEmpty()) {
                    continue; // skip this app
                }
                if (ifCandidates.size() == 1 && pos != null) {
                    TacletApp a = ifCandidates.head();
                    ImmutableList<IfFormulaInstantiation> ifs
                            = a.ifFormulaInstantiations();
                    if (ifs != null && ifs.size() == 1
                            && ifs.head() instanceof IfFormulaInstSeq) {
                        IfFormulaInstSeq ifis = (IfFormulaInstSeq) ifs.head();
                        if (ifis.toPosInOccurrence().equals(
                                pos.topLevel())) {
                            continue; // skip app if find and if same formula
                        }
                    }
                }
            }

            Taclet taclet = app.taclet();
            if (!applicableRules.contains(taclet)) {
                applicableRules.add(taclet);
                result = result.prepend(app);
            }
        }
        return result;
    }
    
       
    
    
    
    
    
    
    
    
    
    



    @Override
    public boolean selectedTaclet(Taclet taclet, Goal goal,
              PosInOccurrence pos) {
   final Services services = goal.proof().getServices();
   ImmutableSet<TacletApp> applics =
         getAppsForName(goal, taclet.name().toString(), pos);
        if (applics.size() == 0) {
           return false;
        }
   Iterator<TacletApp> it = applics.iterator();
   if (applics.size() == 1) {
       TacletApp firstApp = it.next();
            boolean ifSeqInteraction =
               !firstApp.taclet().ifSequent().isEmpty() ;
            if (isMinimizeInteraction() && !firstApp.complete()) {
                ImmutableList<TacletApp> ifSeqCandidates =
                    firstApp.findIfFormulaInstantiations(goal.sequent(),
              services);

                if (ifSeqCandidates.size() == 1) {
                    ifSeqInteraction = false;
                    firstApp = ifSeqCandidates.head();
                }
                TacletApp tmpApp =
                    firstApp.tryToInstantiate(services);
                if (tmpApp != null) firstApp = tmpApp;

            }
       if (ifSeqInteraction || !firstApp.complete()) {
         LinkedList<TacletApp> l = new LinkedList<TacletApp>();
         l.add(firstApp);
            ApplyTacletDialogModel[] models = completeAndApplyApp(l, goal);
         completeAndApplyTacletMatch(models, goal);
       } else {
          applyInteractive(firstApp, goal);
       }
   } else if (applics.size() > 1) {
            java.util.List<TacletApp> appList = new java.util.LinkedList<TacletApp>();

       for (int i = 0; i < applics.size(); i++) {
           TacletApp rapp = it.next();
                appList.add(rapp);
            }

            if (appList.size()==0) {
                 assert false;
                 return false;
            }

            ApplyTacletDialogModel[] models = completeAndApplyApp(
                    appList, goal);

            completeAndApplyTacletMatch(models, goal);

        }
        return true;
    }
    

    @Override
    public void applyInteractive(RuleApp app, Goal goal) {
       goal.node().getNodeInfo().setInteractiveRuleApplication(true);
       goal.apply(app);
    }


    /**
     * collects all Taclet applications at the given position of the specified
     * taclet
     *
     * @param goal the Goal for which the applications should be returned
     * @param name the String with the taclet names whose applications are
     * looked for
     * @param pos the PosInOccurrence describing the position
     * @return a list of all found rule applications of the given rule at
     * position pos
     */
    protected ImmutableSet<TacletApp> getAppsForName(Goal goal, String name,
            PosInOccurrence pos) {
        return getAppsForName(goal, name, pos, TacletFilter.TRUE);
    }

    /**
     * collects all taclet applications for the given position and taclet
     * (identified by its name) matching the filter condition
     *
     * @param goal the Goal for which the applications should be returned
     * @param name the String with the taclet names whose applications are
     * looked for
     * @param pos the PosInOccurrence describing the position
     * @param filter the TacletFilter expressing restrictions
     * @return a list of all found rule applications of the given rule at
     * position <tt>pos</tt> passing the filter
     */
    protected ImmutableSet<TacletApp> getAppsForName(Goal goal, String name,
            PosInOccurrence pos,
            TacletFilter filter) {
        Services services = goal.proof().getServices();
        ImmutableSet<TacletApp> result = DefaultImmutableSet.<TacletApp>nil();
        ImmutableList<TacletApp> fittingApps = ImmutableSLList.<TacletApp>nil();
        final RuleAppIndex index = goal.ruleAppIndex();

        if (pos == null) {
            for (NoPosTacletApp noPosTacletApp : index.getNoFindTaclet(filter,
                    services)) {
                fittingApps = fittingApps.prepend(noPosTacletApp);
            }
        } else {
            fittingApps = index.getTacletAppAt(filter,
                    pos,
                    services);
        }

        // filter fitting applications
        for (TacletApp app : fittingApps) {
            if (app.rule().name().toString().equals(name)) {
                result = result.add(app);
            }
        }
//if (result.size()==0) System.err.println("Available was "+fittingApps);
        return result;
    }
    
    public ApplyTacletDialogModel[] completeAndApplyApp(java.util.List<TacletApp> apps, Goal goal) {
        ApplyTacletDialogModel[] origInstModels = new ApplyTacletDialogModel[apps.size()];
        LinkedList<ApplyTacletDialogModel> recentInstModels = new LinkedList<ApplyTacletDialogModel>();

        int appCounter = 0;
        for (final TacletApp tA : apps) {            
            origInstModels[appCounter] = createModel(tA, goal);

            if (InstantiationFileHandler.hasInstantiationListsFor(tA
                    .taclet())) {
                for (final List<String> instantiations : 
                    InstantiationFileHandler.getInstantiationListsFor(tA.taclet())) {
                    int start = tA.instantiations().size();

                    if (origInstModels[appCounter].tableModel().getRowCount() - start ==
                            instantiations.size()) {
                        ApplyTacletDialogModel m = createModel(tA,
                                goal);
                        recentInstModels.add(m);
                        for (final String inst : instantiations) {
                            m.tableModel().setValueAt(inst, start++, 1);
                        }
                    }
                }
            }
            appCounter++;
        }

        ApplyTacletDialogModel[] models = new ApplyTacletDialogModel[
                origInstModels.length + recentInstModels.size()];
        int i;
        for (i = 0; i < origInstModels.length; i++) {
            models[i] = origInstModels[i];
        }

        for (final ApplyTacletDialogModel model : recentInstModels) {
            models[i++] = model;
        }

        return models;
    }

    public ApplyTacletDialogModel createModel(TacletApp app, Goal goal) {
       final Proof proof = goal.proof();
       
       final Namespace progVars = new Namespace(); 
       final NamespaceSet ns = proof.getNamespaces();
       progVars.add(goal.getGlobalProgVars());
       
       return new ApplyTacletDialogModel(
            app, goal.sequent(), proof.getServices(),
       new NamespaceSet(ns.variables(),
              ns.functions(),
              ns.sorts(),
              ns.ruleSets(),
              ns.choices(),
              progVars),
              proof.abbreviations(),
       goal);
    }
    
    
    
    
    
    
    
    




    @Override
    public void selectedBuiltInRule(Goal goal, BuiltInRule rule, PosInOccurrence pos, boolean forced) {
      assert goal != null;

      ImmutableSet<IBuiltInRuleApp> set = getBuiltInRuleApp(goal, rule, pos);
      if (set.size() > 1) {
         System.err.println("keymediator:: Expected a single app. If " +
               "it is OK that there are more than one " +
               "built-in rule apps. You have to add a " +
               "selection dialog here");
         System.err.println("keymediator:: Ambigous applications, " +
               "taking the first in list.");
      }

      IBuiltInRuleApp app = set.iterator().next();

      if (!app.complete()) {
         app = completeBuiltInRuleApp(app, goal, forced);
      }

      if (app != null && app.rule() == rule) {
         goal.apply(app);
         return;
      }
    }

    /**
     * collects all built-in rule applications for the given rule that are
     * applicable at position 'pos' and the current user constraint
     *
     * @param rule the BuiltInRule for which the applications are collected
     * @param pos the PosInSequent the position information
     * @return a SetOf<IBuiltInRuleApp> with all possible rule applications
     */
    public ImmutableSet<IBuiltInRuleApp> getBuiltInRuleApp(Goal focusedGoal, BuiltInRule rule,
            PosInOccurrence pos) {

        ImmutableSet<IBuiltInRuleApp> result = DefaultImmutableSet.<IBuiltInRuleApp>nil();

        for (final IBuiltInRuleApp app : focusedGoal.ruleAppIndex().
                getBuiltInRules(focusedGoal, pos)) {
            if (app.rule() == rule) {
                result = result.add(app);
            }
        }

        return result;
    }

    /**
     * collects all applications of a rule given by its name at a give position
     * in the sequent
     *
     * @param name the name of the BuiltInRule for which applications are
     * collected.
     * @param pos the position in the sequent where the BuiltInRule should be
     * applied
     * @return a SetOf<RuleApp> with all possible applications of the rule
     */
    protected ImmutableSet<IBuiltInRuleApp> getBuiltInRuleAppsForName(Goal focusedGoal, String name, PosInOccurrence pos) {
        ImmutableSet<IBuiltInRuleApp> result = DefaultImmutableSet.<IBuiltInRuleApp>nil();
        ImmutableList<BuiltInRule> match = ImmutableSLList.<BuiltInRule>nil();

        //get all possible rules for current position in sequent
        ImmutableList<BuiltInRule> list = getBuiltInRule(focusedGoal, pos);

        Iterator<BuiltInRule> iter = list.iterator();

        //find all rules that match given name
        while (iter.hasNext()) {
            BuiltInRule rule = iter.next();
            if (rule.name().toString().equals(name)) {
                match = match.append(rule);
            }
        }

        iter = match.iterator();

        //find all applications for matched rules
        while (iter.hasNext()) {
            result = result.union(getBuiltInRuleApp(focusedGoal, iter.next(), pos));
        }

        return result;
    }
}