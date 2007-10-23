// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Vector;

import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.mgt.BasicTask;
import de.uka.ilkd.key.proof.mgt.DefaultProofCorrectnessMgt;
import de.uka.ilkd.key.proof.mgt.ProofCorrectnessMgt;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;


/**
 * A proof is represented as a tree whose nodes are created by
 * applying rules on the current (open) goals and dividing them up
 * into several new subgoals. To distinguish between open goals (the
 * ones we are working on) and closed goals or inner nodes we restrict
 * the use of the word goal to open goals which are a subset of the
 * proof tree's leaves.  This proof class represents a proof and
 * encapsulates its tree structure.  The {@link Goal} class represents
 * a goal with all needed extra information, and methods to apply
 * rules.  Furthermore it offers services that deliver the open goals,
 * namespaces and several other informations about the current state
 * of the proof.
 */
public class Proof implements Named {

    /** name of the proof */
    private Name name;

    /** the root of the proof */
    private Node root;

    /** 
     * list with prooftree listeners of this proof 
     * attention: firing events makes use of array list's random access
     * nature
     */
    private List listenerList = new ArrayList(10);
    
    /** list with the open goals of the proof */ 
    private ListOfGoal openGoals = SLListOfGoal.EMPTY_LIST;

    /** during closure this can be set by "subTreeCompletelyClosed" */
    private Node closedSubtree = null;
    
    /** declarations &c, read from a problem file or otherwise */
    private String problemHeader = "";

    /** the update simplifier (may be moved to nodes)*/
    private UpdateSimplifier upd_simplifier;

    /** the java information object: JavaInfo+TypeConverter */
    private final Services services;

    /** maps the Abbreviations valid for this proof to their corresponding terms.*/
    private AbbrevMap abbreviations = new AbbrevMap();

    /** User constraint */
    private ConstraintTableModel userConstraint = new ConstraintTableModel ();    

    /** Deliverer for new metavariables */
    private MetavariableDeliverer metavariableDeliverer;

    /** the environment of the proof with specs and java model*/
    private ProofEnvironment proofEnv;
    
    /** the environment of the proof with specs and java model*/
    private ProofCorrectnessMgt localMgt;

    private BasicTask task;
    
    private ProofSettings settings;

    /**
     * when different users load and save a proof this vector fills up with
     * Strings containing the user names.
     * */
    public Vector userLog;

    /** 
     * when load and save a proof with different versions of key this vector
     * fills up with Strings containing the prcs versions.
     */
    public Vector keyVersionLog;
   
    
    private Strategy activeStrategy;
    
    /** constructs a new empty proof with name */
    private Proof(Name name, Services services, ProofSettings settings) {
	this.name = name;
        assert services != null : "Tried to create proof without valid services.";
	this.services = services.copyProofSpecific();
        this.settings = settings;
        
        metavariableDeliverer = new MetavariableDeliverer ( this );
        addConstraintListener ();

        addStrategyListener ();
    }

    /**
     * initialises the strategies
     */
    private void initStrategy() {
        StrategyProperties activeStrategyProperties = 
            settings.getStrategySettings().getActiveStrategyProperties(); 
        
        final Profile profile = settings.getProfile();
        
        if (profile.supportsStrategyFactory(settings.getStrategySettings().getStrategy())) {            
            setActiveStrategy
                (profile.getStrategyFactory(settings.getStrategySettings().
                        getStrategy()).create(this, activeStrategyProperties));
        } else {                            
            setActiveStrategy( 
                profile.getDefaultStrategyFactory().create(this, 
                        activeStrategyProperties));
        }
    }

    /** constructs a new empty proof */
    public Proof(Services services) {
	this ( "", services );
    }


    /** constructs a new empty proof with name */
    public Proof(String name, Services services) {
	this ( new Name ( name ),
               services,
               new ProofSettings ( ProofSettings.DEFAULT_SETTINGS ) );
    }
    
    private Proof(String name, Sequent problem, TacletIndex rules,
            BuiltInRuleIndex builtInRules, Services services,
            ProofSettings settings) {

        this ( new Name ( name ), services, settings );

	localMgt = new DefaultProofCorrectnessMgt(this);

        Node rootNode = new Node(this, problem);
        setRoot(rootNode);

	Goal firstGoal = new Goal(rootNode, 
                                  new RuleAppIndex(new TacletAppIndex(rules),
						   new BuiltInRuleAppIndex(builtInRules)));
	openGoals = openGoals.prepend(firstGoal);

	if (closed())
	    fireProofClosed();
    }
    
    public Proof(String name, Term problem, String header, TacletIndex rules,
         BuiltInRuleIndex builtInRules, Services services, ProofSettings settings) {
        this ( name, Sequent.createSuccSequent
                 (Semisequent.EMPTY_SEMISEQUENT.insert(0, 
                         new ConstrainedFormula(problem)).semisequent()), 
                 rules, builtInRules, services, settings );
        problemHeader = header;
    }
    
    public Proof(String name, Sequent sequent, String header, TacletIndex rules,
            BuiltInRuleIndex builtInRules, Services services, ProofSettings settings) {
        this ( name, sequent, rules, builtInRules, services, settings );
        problemHeader = header;
    }

    
    /** copy constructor */
    public Proof(Proof p) {
        this(p.name, p.env().getInitConfig().getServices(), 
             new ProofSettings(p.settings));
        activeStrategy = 
            StrategyFactory.create(this, 
                    p.getActiveStrategy().name().toString(), 
                    getSettings().getStrategySettings().getActiveStrategyProperties());
        
        InitConfig ic = p.env().getInitConfig();
        Node rootNode = new Node(this, p.root.sequent());
        setRoot(rootNode);
	Goal firstGoal = new Goal(rootNode, 
            new RuleAppIndex(new TacletAppIndex(ic.createTacletIndex()),
	    new BuiltInRuleAppIndex(ic.createBuiltInRuleIndex())));
	localMgt = new DefaultProofCorrectnessMgt(this);
	openGoals = openGoals.prepend(firstGoal);
        setNamespaces(ic.namespaces());       
    }
    

    public Proof (String name,
                  Term problem,
                  String header,
                  TacletIndex rules,
                  BuiltInRuleIndex builtInRules,
                  Services services) {
        this ( name,
               problem,
               header,
               rules,
               builtInRules,
               services,
               new ProofSettings ( ProofSettings.DEFAULT_SETTINGS ) );
    }
         

    /** 
     * returns the name of the proof. Describes in short what has to be proved.     
     * @return the name of the proof
     */
    public Name name() {
	return name;
    }
    
    public String header() {
       return problemHeader;
    }
    
    public ProofCorrectnessMgt mgt() {
	return localMgt;
    }
    
    /** 
     * returns a collection of the namespaces valid for this proof
     */
    public NamespaceSet getNamespaces() {
	return getServices().getNamespaces();
    }

    /** returns the JavaInfo with the java type information */
    public JavaInfo getJavaInfo() {
	return getServices().getJavaInfo();
    }

    /** returns the Services with the java service classes */
    public Services getServices() {
       return services;
    }

    /** sets the variable, function, sort, heuristics namespaces */
    public void setNamespaces(NamespaceSet ns) {
        getServices().setNamespaces(ns);
        if (openGoals().size() > 1)
            throw new IllegalStateException("Proof: ProgVars set too late");
        openGoals().head().addProgramVariables(ns.programVariables());
    }

    public void setBasicTask(BasicTask t) {
	task = t;
    }

    public BasicTask getBasicTask() {
	return task;
    }

    public AbbrevMap abbreviations(){
	return abbreviations;
    }
   
    public Strategy getActiveStrategy() {
        if (activeStrategy == null) {
            initStrategy();
        }
        return activeStrategy;
    }

    public void setActiveStrategy(Strategy activeStrategy) {
        this.activeStrategy = activeStrategy;
        getSettings().getStrategySettings().
            setStrategy(activeStrategy.name());
        updateStrategyOnGoals();
    }
 
    
    private void updateStrategyOnGoals() {
        Strategy ourStrategy = getActiveStrategy();
        
        final IteratorOfGoal it = openGoals ().iterator ();
        while ( it.hasNext () )
            it.next ().setGoalStrategy(ourStrategy);
    }

    /** 
     * returns the default simplifier to be used (may be overwritten by branch
     * specific simplifiers in the future)
     * @return the UpdateSimplifier to be used as default one
     */
    public UpdateSimplifier simplifier() {
	return upd_simplifier;
    }

    /** 
     * sets the default simplifier
     * @param upd_simplifier the UpdateSimplifier to be used as
     * default (may be overwritten by branch specific simplifiers in the future)
     */
    public void setSimplifier(UpdateSimplifier upd_simplifier) {
	this.upd_simplifier = upd_simplifier;
    }

    /** returns the user constraint (table model)
     * @return the user constraint
     */
    public ConstraintTableModel getUserConstraint() {
	return userConstraint;
    }

    private void addConstraintListener() {
	getUserConstraint ()
	    .addConstraintTableListener ( new ConstraintTableListener () {
		    public void constraintChanged ( ConstraintTableEvent e ) {
			clearAndDetachRuleAppIndexes ();
		}
	    });
    }
    
    private void addStrategyListener () {
        getSettings().getStrategySettings()
            .addSettingsListener ( new SettingsListener () {
                public void settingsChanged ( GUIEvent config ) {
                    updateStrategyOnGoals();
                }
            });
    }

    private void clearAndDetachRuleAppIndexes () {
        // Taclet indices of the particular goals have to
        // be rebuilt
        final IteratorOfGoal it = openGoals ().iterator ();
        while ( it.hasNext () )
            it.next ().clearAndDetachRuleAppIndex ();
    }
    
    /** @return Deliverer of new metavariables (with unique names)*/
    public MetavariableDeliverer getMetavariableDeliverer () {
	return metavariableDeliverer;
    }
    
    public JavaModel getJavaModel() {
        return proofEnv.getJavaModel();
    }

    public void setProofEnv(ProofEnvironment env) {
	proofEnv=env;
    }

    public ProofEnvironment env() {
	return proofEnv;
    }

    /**
     * returns the root node of the proof
     */
    public Node root() {
	return root;
    }

    /** sets the root of the proof */
    public void setRoot(Node root) {
	if (this.root != null) {
	    throw new IllegalStateException
		("Tried to reset the root of the proof.");
	} else {
	    this.root = root;
	    fireProofStructureChanged();

	    if (closed())
		fireProofClosed();
	}
    }
    
    public void setSettings(ProofSettings newSettings) {
        settings = newSettings;
        addStrategyListener ();
    }
    
    public ProofSettings getSettings() {
        return settings;
    }


    /** 
     * returns the list of open goals
     * @return list with the open goals
     */
    public ListOfGoal openGoals() {
	return openGoals;
    }

    /** 
     * removes the given goal and adds the new goals in list 
     * @param oldGoal the old goal that has to be removed from list
     * @param newGoals the ListOfGoal with the new goals that were
     * result of a rule application on goal
     */
    public void replace(Goal oldGoal, ListOfGoal newGoals) {
	openGoals = openGoals.removeAll(oldGoal);

	if ( closed () )
	    fireProofClosed();
	else {
	    fireProofGoalRemoved(oldGoal);
	    add(newGoals);	
	}
    }

    /**
     * Add the given constraint to the closure constraint of the given
     * goal, i.e. the given goal is closed if p_c is satisfied.
     */
    public void closeGoal ( Goal p_goal, Constraint p_c ) {
	p_goal.addClosureConstraint ( p_c );

	removeClosedSubtree ();

	if ( closed () )
	    fireProofClosed();
    }

    /**
     * This is called by a Node that is the root of a subtree that is
     * closed
     */
    public void subtreeCompletelyClosed ( Node p_node ) {
	// This method will be called for nodes with increasing
	// distance to the root
	if ( closedSubtree == null )
	    closedSubtree = p_node;
    }

    /**
     * Use this information to remove the goals of the closed subtree
     */
    protected void removeClosedSubtree () {
	// give the information that a subtree is closed
	// to all nodes below this node
	if (closedSubtree != null) 
	    closedSubtree.setClosed();

	if ( !closed () && closedSubtree != null ) {

	    boolean        b    = false;
	    IteratorOfNode it   = closedSubtree.leavesIterator ();
	    Goal           goal;

	    while ( it.hasNext () ) {
		goal = getGoal ( it.next () );
		if ( goal != null ) {
		    b = true;
		    remove ( goal );
		}
	    }

	    if ( b )
		// For the moment it is necessary to fire the message ALWAYS
		// in order to detect branch closing.
		fireProofGoalsAdded ( SLListOfGoal.EMPTY_LIST );		
	}

	closedSubtree = null;
    }

    /** removes the given goal from the list of open goals. Take care
     * removing the last goal will fire the proofClosed event
     * @param goal the Goal to be removed
     */
    public void remove(Goal goal) {
	ListOfGoal newOpenGoals = openGoals.removeAll(goal);
	if (newOpenGoals != openGoals) {
	    openGoals = newOpenGoals;	
	    if (closed()) {
		fireProofClosed();
	    } else {
		fireProofGoalRemoved(goal);
	    }
	}
    }

    /** adds a new goal to the list of goals 
     * @param goal the Goal to be added 
     */
    public void add(Goal goal) {
	ListOfGoal newOpenGoals = openGoals.prepend(goal);
	if (openGoals != newOpenGoals) {
	    openGoals = newOpenGoals;
	    fireProofGoalsAdded(goal);
	}
    }

    /** adds a list with new goals to the list of open goals 
     * @param goals the ListOfGoal to be prepended 
     */
    public void add(ListOfGoal goals) {
	ListOfGoal newOpenGoals = openGoals.prepend(goals);
	if (openGoals != newOpenGoals) {
	    openGoals = newOpenGoals;
	}

	// For the moment it is necessary to fire the message ALWAYS
	// in order to detect branch closing.
	fireProofGoalsAdded(goals);
	
    }

    /** Return whether the remaining goals can be closed, i.e. whether
     * the conjunction of the constraints of the open goals is
     * satisfiable. In this case all remaining open goals are removed.
     */
    public boolean closed () {
	if ( root ().getRootSink ().isSatisfiable () ) {
	    Goal goal;
	    while ( openGoals != SLListOfGoal.EMPTY_LIST ) {
		goal      = openGoals.head ();
		openGoals = openGoals.tail ();
		fireProofGoalRemoved ( goal );
	    }
	    return true;
	}
	return false;
    }
    
    
    /** returns true iff sets back to the step that created the given
     * goal. If the undo operation was succesful true is returned.
     * @param goal the Goal desribing the location where to set back
     * @return true iff undo operation was succesfull.
     */
    public boolean setBack(Goal goal) {		
	if (goal != null) {
	    Node parent = goal.node().parent();
	    if (parent != null) {
                getServices().setBackCounters(goal.node());
		openGoals = goal.setBack(openGoals);
		fireProofGoalsChanged();
		return true;
	    }
	}
	// root reached or proof closed
	return false;
    }

    /** Prunes away the subtree beneath <code>node</code>.
     *	<code>node</code> is going to be the last node on its
     * branch.
     * @param node the node desribing the location where to set back
     * @return true iff undo operation was succesfull.
     */
    public boolean setBack(Node node) {
	final Goal goal = getGoal(node);
	if (goal!=null) {
	    return true;
	} else {
	    final ListOfGoal goalList = getSubtreeGoals(node);
	    if (!goalList.isEmpty()) {
		// The subtree goals (goalList) are scanned for common
		// direct ancestors (parents). Afterwards the remove
		// list is the greatest subset of the subtree goals such
		// that the parents of the goals are disjoint.
		final HashSet parentSet = new HashSet();		
		final IteratorOfGoal goalIt = goalList.iterator();
                ListOfGoal removeList = SLListOfGoal.EMPTY_LIST;
		while (goalIt.hasNext()) {
		    final Goal nextGoal = goalIt.next();
		    if (!parentSet.contains(nextGoal.node().parent())) {
			removeList = removeList.prepend(nextGoal);
			parentSet.add(nextGoal.node().parent());
		    }
		}
		//call setBack(Goal) on each element in the remove
		//list. The former parents become the new goals
		final IteratorOfGoal removeIt = removeList.iterator();
		while (removeIt.hasNext()) {
		    setBack(removeIt.next());
		}
		return setBack(node);
	    }
	    return false;
	}
    }

    // ?? seems to be required for presentation uses
    // I think there is a mismatch between what the method does and the method's
    // name. Can the one who implemented this method check the name and write a
    // short comment about its purpose %%RB
    public void updateProof() {
	fireProofGoalsChanged();
    }


    /** fires the event that the proof has been expanded at the given node */
    protected void fireProofExpanded(Node node) {
	ProofTreeEvent e = new ProofTreeEvent(this, node);
	for (int i = 0; i<listenerList.size(); i++) {
	    ((ProofTreeListener)listenerList.get(i)).proofExpanded(e);
	}
    }

    /** fires the event that the proof has been pruned at the given node */
    protected void fireProofPruned(Node node, Node removedNode) {
	ProofTreeEvent e = new ProofTreeRemovedNodeEvent(this, node, removedNode);
	for (int i = 0; i<listenerList.size(); i++) {
	    ((ProofTreeListener)listenerList.get(i)).proofPruned(e);
	}
    } 

    /** fires the event that the proof has been restructured */
    protected void fireProofStructureChanged() {
	ProofTreeEvent e = new ProofTreeEvent(this);
	for (int i = 0; i<listenerList.size(); i++) {
	    ((ProofTreeListener)listenerList.get(i)).proofStructureChanged(e);
	}    
    }

    /** fires the event that a goal has been removed from the list of goals */
    protected void fireProofGoalRemoved(Goal goal) {
	ProofTreeEvent e = new ProofTreeEvent(this, goal);
	for (int i = 0; i<listenerList.size(); i++) {
	    ((ProofTreeListener)listenerList.get(i)).proofGoalRemoved(e);
	}	
    }

    /** fires the event that new goals have been added to the list of
     * goals 
     */
    protected void fireProofGoalsAdded(ListOfGoal goals) {
	ProofTreeEvent e = new ProofTreeEvent(this, goals);
	for (int i = 0; i<listenerList.size(); i++) {
	    ((ProofTreeListener)listenerList.get(i)).proofGoalsAdded(e);
	}	
    }

    /** fires the event that new goals have been added to the list of
     * goals 
     */
    protected void fireProofGoalsAdded(Goal goal) {
	fireProofGoalsAdded(SLListOfGoal.EMPTY_LIST.prepend(goal));
    }

    /** fires the event that the proof has been restructured */
    protected void fireProofGoalsChanged() {
	ProofTreeEvent e = new ProofTreeEvent(this, openGoals());
	for (int i = 0; i<listenerList.size(); i++) {
	    ((ProofTreeListener)listenerList.get(i)).proofGoalsChanged(e);
	}
    } 

    /** fires the event that the proof has closed. 
     * This event fired instead of the proofGoalRemoved event when
     * the last goal in list is removed.
     */
    protected void fireProofClosed() {
	ProofTreeEvent e = new ProofTreeEvent(this);
	for (int i = 0; i<listenerList.size(); i++) {
	    ((ProofTreeListener)listenerList.get(i)).proofClosed(e);
	}
    }

    /**
     * adds a listener to the proof 
     * @param listener the ProofTreeListener to be added
     */
    public synchronized void addProofTreeListener
	(ProofTreeListener listener) {
	synchronized(listenerList) {
	    listenerList.add(listener);
	}
    }

    /**
     * removes a listener from the proof 
     * @param listener the ProofTreeListener to be removed
     */
    public synchronized void removeProofTreeListener
	(ProofTreeListener listener) {
	synchronized(listenerList) {
	    listenerList.remove(listener);
	}
    }
    
    public synchronized boolean containsProofTreeListener(ProofTreeListener listener) {
        synchronized(listenerList) {
            return listenerList.contains(listener);
        }
    }

    /** returns true if the given node is part of a Goal 
     * @return  true if the given node is part of a Goal 
     */
    public boolean isGoal(Node node) {	
	return getGoal(node) != null;
    }

    /** returns the goal that belongs to the given node or null if the
     * node is an inner one 
     * @return the goal that belongs to the given node or null if the
     * node is an inner one 
     */
    public Goal getGoal(Node node) {	
	Goal result = null;
	IteratorOfGoal it = openGoals.iterator();
	while (it.hasNext()) {
	    result = it.next();
	    if (result.node() == node) {
		return result;
	    }
	}
	return null;
    }

    /** returns the list of goals of the subtree starting with node 
     * @param node the Node where to start from
     * @return the list of goals of the subtree starting with node 
     */
    public ListOfGoal getSubtreeGoals(Node node) {	
	ListOfGoal result = SLListOfGoal.EMPTY_LIST;
	final IteratorOfGoal goalsIt  = openGoals.iterator();
	while (goalsIt.hasNext()) {
	    final Goal goal = goalsIt.next();
	    final IteratorOfNode leavesIt = node.leavesIterator();
	    while (leavesIt.hasNext()) {
		if (leavesIt.next() == goal.node()) {
		    result = result.prepend(goal);
		}
	    }
	}
	return result;
    }

    /** returns true iff the given node is found in the proof tree 
     *	@param node the Node to search for
     *	@return true iff the given node is found in the proof tree 
    */
    public boolean find(Node node) {
	if (root == null) {
	    return false;
	}
	return root.find(node);
    }

    /**
     * retrieves number of nodes
     */
    public int countNodes() {
	return root.countNodes();
    }

    /**
     * Currently the rule app index can either operate in interactive mode (and
     * contain applications of all existing taclets) or in automatic mode (and
     * only contain a restricted set of taclets that can possibly be applied
     * automated). This distinction could be replaced with a more general way to
     * control the contents of the rule app index
     */
    public void setRuleAppIndexToAutoMode () {
	IteratorOfGoal it = openGoals.iterator ();
	while ( it.hasNext () ) {
	    it.next ().ruleAppIndex ().autoModeStarted ();
	}
    }

    public void setRuleAppIndexToInteractiveMode () {
	IteratorOfGoal it = openGoals.iterator ();
	while ( it.hasNext () ) {
	    it.next ().ruleAppIndex ().autoModeStopped ();
	}
    }
    
    public void addRuleSource(RuleSource src) {
        problemHeader += src.getInclusionString()+"\n";
    }
    
    

    /**
     * retrieves number of branches
     */
    public int countBranches() {
	return root.countBranches();
    }

    public String statistics() {
	return "Nodes:"  + countNodes() + "\n" +
	    "Branches: " + countBranches() + "\n";
    }

    /** toString */
    public String toString() {
	StringBuffer result = new StringBuffer();
	    result.append("Proof -- ");
	    if (!"".equals(name.toString())) {
		result.append(name.toString());
	    } else {
		result.append("unnamed");
	    }
	result.append("\nProoftree:\n");
	result.append(root.toString());
	return result.toString();
    }

  
}
