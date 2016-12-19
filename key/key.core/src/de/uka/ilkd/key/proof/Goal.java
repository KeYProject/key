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

package de.uka.ilkd.key.proof;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.proofevent.NodeChangeJournal;
import de.uka.ilkd.key.proof.proofevent.RuleAppInfo;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.strategy.AutomatedRuleApplicationManager;
import de.uka.ilkd.key.strategy.QueueRuleApplicationManager;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.util.properties.MapProperties;
import de.uka.ilkd.key.util.properties.Properties;
import de.uka.ilkd.key.util.properties.Properties.Property;

/**
 *  A proof is represented as a tree of nodes containing sequents. The initial
 *  proof consists of just one node -- the root -- that has to be
 *  proved. Therefore it is divided up into several sub goals and so on. A
 *  single goal is not divided into sub goals any longer if the contained
 *  sequent becomes an axiom. A proof is closed if all leaves are closed. As
 *  the calculus works only on the leaves of a tree, the goals are the
 *  additional information needed for the proof is only stored at the leaves
 *  (saves memory) and not in the inner nodes. This class represents now a goal
 *  of the proof, this means a leave whose sequent is not closed. It keeps
 *  track of all applied rule applications on the branch and of the
 *  corresponding rule application index. Furthermore it offers methods for
 *  setting back several proof steps. The sequent has to be changed using the
 *  methods of Goal.
 */
public final class Goal  {

    private Node node;

    /** all possible rule applications at this node are managed with this index */
    private RuleAppIndex ruleAppIndex;

    /** list of all applied rule applications at this branch */
    private ImmutableList<RuleApp> appliedRuleApps = ImmutableSLList.<RuleApp>nil();

    /** this object manages the tags for all formulas of the sequent */
    private FormulaTagManager tagManager;

    /** the strategy object that determines automated application of rules */
    private Strategy goalStrategy = null;

    /** */
    private AutomatedRuleApplicationManager ruleAppManager;

    /** goal listeners  */
    private List<GoalListener> listeners = new ArrayList<GoalListener>(10);

    /** a goal has been excluded from automatic rule application iff automatic == false */
    private boolean automatic = true;
    
    /** Marks this goal as linked (-> join rules) */
    private Goal linkedGoal   = null;

    /**
     * If an application of a rule added some information for the strategy,
     * then this information is stored in this map.
     */
    private final Properties strategyInfos;

    /** creates a new goal referencing the given node */
    private Goal(Node node,
                 RuleAppIndex ruleAppIndex,
                 ImmutableList<RuleApp> appliedRuleApps,
                 FormulaTagManager tagManager,
                 AutomatedRuleApplicationManager ruleAppManager,
                 Properties strategyInfos) {
        this.node = node;
        this.ruleAppIndex = ruleAppIndex;
        this.appliedRuleApps = appliedRuleApps;
        this.tagManager = tagManager;
        this.goalStrategy = null;
        this.ruleAppIndex.setup(this);
        this.strategyInfos = strategyInfos;
        setRuleAppManager(ruleAppManager);
    }

    private Goal(Node node,
                 RuleAppIndex ruleAppIndex,
                 ImmutableList<RuleApp> appliedRuleApps,
                 AutomatedRuleApplicationManager ruleAppManager,
                 Properties strategyInfos) {
      this.node            = node;
      this.ruleAppIndex    = ruleAppIndex;
      this.appliedRuleApps = appliedRuleApps;
      this.goalStrategy    = null;
      this.ruleAppIndex.setup ( this );
      this.strategyInfos = strategyInfos;
      setRuleAppManager ( ruleAppManager );
      this.tagManager      = new FormulaTagManager ( this );;
      }
    
    /**
     * creates a new goal referencing the given node
     */
    public Goal (Node node, RuleAppIndex ruleAppIndex) {
        this ( node,
               ruleAppIndex,
               ImmutableSLList.<RuleApp>nil(),
               null,
               new QueueRuleApplicationManager (),
               new MapProperties());
        tagManager = new FormulaTagManager ( this );
    }

    /** this object manages the tags for all formulas of the sequent */
    public FormulaTagManager getFormulaTagManager () {
    	return tagManager;
    }

    /**
     * @return the strategy that determines automated rule applications for this
     * goal
     */
    public Strategy getGoalStrategy () {
        if ( goalStrategy == null )
            goalStrategy = proof ().getActiveStrategy ();
        return goalStrategy;
    }

    public void setGoalStrategy ( Strategy p_goalStrategy ) {
        goalStrategy = p_goalStrategy;
        ruleAppManager.clearCache ();
    }

    public AutomatedRuleApplicationManager getRuleAppManager () {
    	return ruleAppManager;
    }

    public void setRuleAppManager(AutomatedRuleApplicationManager manager) {
        if ( ruleAppManager != null ) {
            ruleAppIndex ().removeNewRuleListener ( ruleAppManager );
            ruleAppManager.setGoal ( null );
        }

        ruleAppManager = manager;

        if ( ruleAppManager != null ) {
            ruleAppIndex ().addNewRuleListener ( ruleAppManager );
            ruleAppManager.setGoal ( this );
        }
    }

    /**
     * returns the referenced node
     */
    public Node node() {
	return node;
    }

    public ImmutableSet<ProgramVariable> getGlobalProgVars() {
	return node.getGlobalProgVars();
    }

    /**
     * adds the listener l to the list of goal listeners.
     * Attention: A listener added to this goal will be taken over when
     * splitting into subgoals.
     * @param l the GoalListener to be added
     */
    public void addGoalListener(GoalListener l) {
	listeners.add(l);
    }

    /**
     * removes the listener l from the list of goal listeners.
     * Attention: The listener is just removed from 'this' goal not from the
     * other goals. (All goals can be accessed via proof openGoals())
     * @param l the GoalListener to be removed
     */
    public void removeGoalListener(GoalListener l) {
       listeners.remove(l);
    }

    /**
     * informs all goal listeners about a change of the sequent
     * to reduce unnecessary object creation the necessary information is passed
     * to the listener as parameters and not through an event object.
     */
    protected void fireSequentChanged(SequentChangeInfo sci) {
	getFormulaTagManager().sequentChanged(this, sci);
	ruleAppIndex()        .sequentChanged(this, sci);
	for (GoalListener listener : listeners) {
	    listener.sequentChanged(this, sci);
	}
    }

    protected void fireGoalReplaced(Goal       goal,
				    Node       parent,
				    ImmutableList<Goal> newGoals) {
	for (GoalListener listener : listeners) {
	    listener.goalReplaced(goal, parent, newGoals);
	}
    }

   protected void fireAautomaticStateChanged(boolean oldAutomatic, boolean newAutomatic) {
      for (GoalListener listener : listeners) {
         listener.automaticStateChanged(this, oldAutomatic, newAutomatic);
      }
   }

  
    public void setGlobalProgVars(ImmutableSet<ProgramVariable> s) {
        assert node.proof().getNamespaces().contains(names(s)) :
                    "\""+names(s)+ "\" not found in namespace.";
        node.setGlobalProgVars(s);
    }

    /**
     * set the node the goal is related to
     * @param p_node the Node in the proof tree to which this goal
     * refers to
     */
    private void setNode(Node p_node) {
	if ( node ().sequent () != p_node.sequent () ) {
	    node = p_node;
	    resetTagManager();
	} else
	    node = p_node;
	ruleAppIndex.setup ( this );
    }

    /**
     * returns the index of possible rule applications at this node
     */
    public RuleAppIndex ruleAppIndex() {
	return ruleAppIndex;
    }

    /**
     * returns the Taclet index for this goal. This is just a shortcut to the
     * Taclet index of the RuleAppIndex
     * @return the Taclet index assigned to this goal
     */
    public TacletIndex indexOfTaclets() {
	return ruleAppIndex.tacletIndex();
    }


    /** returns set of rules applied at this branch
     * @return IList<RuleApp> applied rule applications
     */
    public ImmutableList<RuleApp> appliedRuleApps() {
	return appliedRuleApps;
    }


    /**
     * @return the current time of this goal (which is just the number of
     * applied rules)
     */
    public long getTime () {
    	return appliedRuleApps().size();
    }

    /** returns the proof the goal belongs to
     * @return the Proof the goal belongs to
     */
    public Proof proof() {
        return node().proof();
    }

    /** returns the sequent of the node
     * @return the Sequent to be proved
     */
    public Sequent sequent() {
	return node().sequent();
    }

    /**
     * Checks if is an automatic goal.
     *
     * @return true, if is automatic
     */
    public boolean isAutomatic() {
        return automatic;
    }

    /**
     * Sets the automatic status of this goal.
     *
     * @param t
     *                the new status: true for automatic, false for interactive
     */
    public void setEnabled(boolean t) {
        boolean oldAutomatic = automatic;
        automatic = t;
        node().clearNameCache();
        fireAautomaticStateChanged(oldAutomatic, automatic);
    }

    /**
     * Checks if is this node is linked to another
     * node (for example due to a join operation).
     *
     * @return true iff this goal is linked to another node.
     */
    public boolean isLinked() {
        return this.linkedGoal != null;
    }

    /**
     * Returns the goal that this goal is linked to.
     *
     * @return The goal that this goal is linked to (or null if there is no such one).
     */
    public Goal getLinkedGoal() {
        return this.linkedGoal;
    }

    /**
     * Sets the node that this goal is linked to; also sets this for
     * all parents.
     * 
     * TODO: Check whether it is problematic when multiple child nodes
     * of a node are linked; in this case, the linkedNode field would
     * be overwritten.
     * 
     * @param linkedGoal The goal that this goal is linked to.
     */
    public void setLinkedGoal(final Goal linkedGoal) {
        this.linkedGoal = linkedGoal;
    }

    /**
     * sets the sequent of the node
     * @param sci SequentChangeInfo containing the sequent to be set and
     * desribing the applied changes to the sequent of the parent node
     */
    public void setSequent(SequentChangeInfo sci) {
        node().setSequent(sci.sequent());
//VK reminder: now update the index
       	fireSequentChanged(sci);
    }


    /** adds a formula to the sequent before the given position
     * and informs the rule application index about this change
     * @param cf the SequentFormula to be added
     * @param p PosInOccurrence encodes the position
     */
    public void addFormula(SequentFormula cf, PosInOccurrence p) {
       setSequent(sequent().addFormula(cf, p));
    }


    /** adds a formula to the antecedent or succedent of a
     * sequent. Either at its front or back
     * and informs the rule application index about this change
     * @param cf the SequentFormula to be added
     * @param inAntec boolean true(false) if SequentFormula has to be
     * added to antecedent (succedent)
     * @param first boolean true if at the front, if false then cf is
     * added at the back
     */
    public void addFormula ( SequentFormula cf, boolean inAntec,
          boolean first ) {
       setSequent(sequent().addFormula(cf, inAntec, first));
    }

    /**
     * replaces a formula at the given position
     * and informs the rule application index about this change
     * @param cf the SequentFormula replacing the old one
     * @param p the PosInOccurrence encoding the position
     */
    public void changeFormula(SequentFormula cf, PosInOccurrence p) {
       setSequent(sequent().changeFormula(cf, p));
    }


    /** removes a formula at the given position from the sequent
     * and informs the rule appliccation index about this change
     * @param p PosInOccurrence encodes the position
     */
    public void removeFormula(PosInOccurrence p) {
       setSequent(sequent().removeFormula(p));
    }

    /**
     * puts the NoPosTacletApp to the set of TacletApps at the node
     * of the goal and to the current RuleAppIndex.
     * @param app the TacletApp
     */
    public void addNoPosTacletApp(NoPosTacletApp app) {
	node().addNoPosTacletApp(app);
	ruleAppIndex.addNoPosTacletApp(app);
    }

    /**
     * creates a new TacletApp and puts it to the set of TacletApps at the node
     * of the goal and to the current RuleAppIndex.
     * @param rule the Taclet of the TacletApp to create
     * @param insts the given instantiations of the TacletApp to be created
     */
    public void addTaclet(Taclet           rule,
          SVInstantiations insts,
          boolean          isAxiom) {
       NoPosTacletApp tacletApp =
             NoPosTacletApp.createFixedNoPosTacletApp(rule,
                   insts,
                   proof().getServices());
       if (tacletApp != null) {
          addNoPosTacletApp(tacletApp);
          if (proof().getInitConfig() != null) { // do not break everything
             // because of ProofMgt
             proof().getInitConfig().registerRuleIntroducedAtNode(
                   tacletApp,
                   node.parent() != null ? node.parent() : node,
                         isAxiom);
          }
       }
    }

    /**
     * Rebuild all rule caches
     */
    public void updateRuleAppIndex () {
        getRuleAppManager ().clearCache ();
        ruleAppIndex.clearIndexes ();
    }

    /**
     * Rebuild all rule caches
     */
    public void clearAndDetachRuleAppIndex () {
        getRuleAppManager ().clearCache ();
        ruleAppIndex.clearAndDetachCache ();
    }

    public void addProgramVariable(ProgramVariable pv) {
       proof().getNamespaces().programVariables().addSafely(pv);
	node.setGlobalProgVars(getGlobalProgVars().add(pv));
    }

    public void setProgramVariables(Namespace ns) {
	final Iterator<Named> it=ns.elements().iterator();
	ImmutableSet<ProgramVariable> s = DefaultImmutableSet.<ProgramVariable>nil();
	while (it.hasNext()) {
	    s = s.add((ProgramVariable)it.next());
	}
        node().setGlobalProgVars(DefaultImmutableSet.<ProgramVariable>nil());
        proof().getNamespaces().programVariables().set(s);
        setGlobalProgVars(s);
    }

    /**
     * clones the goal (with copy of tacletindex and ruleAppIndex)
     * @param node the new Node to which the goal is attached
     * @return Object the clone
     */
    @SuppressWarnings("unchecked")
    public Goal clone(Node node) {
        Goal clone;
        if (node.sequent() != this.node.sequent()) {
            clone = new Goal (node,
                    ruleAppIndex.copy(),
                    appliedRuleApps,
                    ruleAppManager.copy(),
                    strategyInfos.clone());
        } else {
            clone = new Goal (node,
                    ruleAppIndex.copy(),
                    appliedRuleApps,
                    getFormulaTagManager().copy(),
                    ruleAppManager.copy(),
                    strategyInfos.clone());
        }
        clone.listeners = (List<GoalListener>)
                ((ArrayList<GoalListener>) listeners).clone();
        clone.automatic = this.automatic;
        return clone;
    }

    /** like the clone method but returns right type
     * @return Goal clone of this Goal
     * @throws CloneNotSupportedException 
     */
    public Goal copy() throws CloneNotSupportedException {
        return (Goal)clone();
    }

    
    /**
     * puts a RuleApp to the list of the applied rule apps at this goal
     * and stores it in the node of the goal
     * @param app the applied rule app
     */
    public void addAppliedRuleApp(RuleApp app) {
	// Last app first makes inserting and searching faster
	appliedRuleApps = appliedRuleApps.prepend(app);
	node().setAppliedRuleApp(app);
    }

    /**
     * PRECONDITION: appliedRuleApps.size () > 0
     */
    public void removeLastAppliedRuleApp () {
	appliedRuleApps = appliedRuleApps.tail ();
	//node ().setAppliedRuleApp ( null );
    }



    /** creates n new nodes as children of the
     * referenced node and new
     * n goals that have references to these new nodes.
     * @return the list of new created goals.
     */
    public ImmutableList<Goal> split(int n) {
	ImmutableList<Goal> goalList=ImmutableSLList.<Goal>nil();
	
	final Node parent = node; // has to be stored because the node
	// of this goal will be replaced
	
	if (n == 1) {
	    Node newNode = new Node(parent.proof(),
                parent.sequent(),
                parent);

        // newNode.addNoPosTacletApps(parent.getNoPosTacletApps());
        newNode.setGlobalProgVars(parent.getGlobalProgVars());
        parent.add(newNode);
        this.setNode(newNode);
        goalList = goalList.prepend(this);  
	} else if (n > 1) { // this would also work for n ==1 but the above avoids unnecessary creation of arrays
	    Node[] newNode = new Node[n];

	    for (int i = 0; i<n; i++) {
	        // create new node and add to tree
	        newNode[i] = new Node(parent.proof(),
	                parent.sequent(),
	                parent);

	        // newNode[i].addNoPosTacletApps(parent.getNoPosTacletApps());
	        newNode[i].setGlobalProgVars(parent.getGlobalProgVars());
	    }

        parent.addAll(newNode);

        this.setNode(newNode[0]);
        goalList = goalList.prepend(this);      
	    
        for (int i = 1; i<n; i++) {
            goalList = goalList.prepend(clone(newNode[i]));	    
        }	    
	}

	fireGoalReplaced ( this, parent, goalList );

	return goalList;
    }

    private void resetTagManager() {
        tagManager = new FormulaTagManager ( this );
    }

    public void setBranchLabel(String s) {
        node.getNodeInfo().setBranchLabel(s);
    }

    void pruneToParent(){
            setNode(node().parent());
            removeLastAppliedRuleApp();
    }

    public ImmutableList<Goal> apply(final RuleApp ruleApp ) {

        final Proof proof = proof();

        final NodeChangeJournal journal = new NodeChangeJournal(proof, this);
        addGoalListener(journal);
      

        final Node n = node;

        final ImmutableList<Goal> goalList = ruleApp.execute(this, proof.getServices());

        proof.getServices().saveNameRecorder(n);

        if (goalList != null){
            if (goalList.isEmpty() ) {
                proof.closeGoal ( this );
            } else {
                proof.replace ( this, goalList );
                if ( ruleApp instanceof TacletApp &&
                        ((TacletApp)ruleApp).taclet ().closeGoal () )
                    // the first new goal is the one to be closed
                    proof.closeGoal ( goalList.head () );
            }
        }

        final RuleAppInfo ruleAppInfo = journal.getRuleAppInfo(ruleApp);

        if ( goalList != null )
            proof.fireRuleApplied( new ProofEvent ( proof, ruleAppInfo ) );
        return goalList;
    }

    public String toString() {
        de.uka.ilkd.key.pp.LogicPrinter lp = (new de.uka.ilkd.key.pp.LogicPrinter
                (new de.uka.ilkd.key.pp.ProgramPrinter(null),
                        new NotationInfo(),
                        proof().getServices()));
        lp.printSequent(node.sequent());
	return lp.toString();
    }

    private <T extends Named> ImmutableSet<Name> names(ImmutableSet<T> set) {
        ImmutableList<Name> names = ImmutableSLList.nil();
        for (T elem : set) {
            names = names.prepend(elem.name());
        }
        return DefaultImmutableSet.fromImmutableList(names);
    }

    public <T> T getStrategyInfo(Property<T> property) {
        return strategyInfos.get(property);
    }


    public <T> void addStrategyInfo(Property<T> property,
                                    T info,
                                    StrategyInfoUndoMethod undoMethod) {
        strategyInfos.put(property, info);
        node.addStrategyInfoUndoMethod(undoMethod);
    }


    public void undoStrategyInfoAdd(StrategyInfoUndoMethod undoMethod) {
        undoMethod.undo(strategyInfos);
    }

    /**
     * Checks if the {@link Goal} has applicable rules.
     * @param goal The {@link Goal} to check.
     * @return {@code true} has applicable rules, {@code false} no rules are applicable.
     */
    public static boolean hasApplicableRules(Goal goal) {
       return goal.getRuleAppManager().peekNext() != null;
    }
}