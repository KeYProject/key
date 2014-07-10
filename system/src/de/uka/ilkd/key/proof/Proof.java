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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.Vector;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.RuleAppListener;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.mgt.ProofCorrectnessMgt;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.ContractRuleApp;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.OneStepSimplifier.Protocol;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.UseDependencyContractApp;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.EnhancedStringBuffer;
import de.uka.ilkd.key.util.Pair;


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
    private List<ProofTreeListener> listenerList = new LinkedList<ProofTreeListener>();

    /** list with the open goals of the proof */
    private ImmutableList<Goal> openGoals = ImmutableSLList.<Goal>nil();

    /** declarations &c, read from a problem file or otherwise */
    private String problemHeader = "";

    /** the proof environment (optional) */
    private ProofEnvironment env;
    
   /** maps the Abbreviations valid for this proof to their corresponding terms.*/
    private AbbrevMap abbreviations = new AbbrevMap();

    /** the logic configuration for this proof, i.e., logic signature, rules etc.*/
    private InitConfig initConfig;    
    
    /** the environment of the proof with specs and java model*/
    private ProofCorrectnessMgt localMgt;

    private ProofSettings settings;
    private ProofIndependentSettings pis;
    /**
     * when different users load and save a proof this vector fills up with
     * Strings containing the user names.
     * */
    public Vector<String> userLog;

    /**
     * when load and save a proof with different versions of key this vector
     * fills up with Strings containing the GIT versions.
     */
    public Vector<String> keyVersionLog;

    private long autoModeTime = 0;

    private Strategy activeStrategy;

    private SettingsListener settingsListener;

    /**
     * Set to true if the proof has been abandoned and the dispose method has
     * been called on this object.
     */
    private boolean disposed = false;

    /** list of rule app listeners */
    private List<RuleAppListener> ruleAppListenerList = Collections.synchronizedList(new ArrayList<RuleAppListener>(10));

    /**
     * Contains all registered {@link ProofDisposedListener}.
     */
    private final List<ProofDisposedListener> proofDisposedListener = new LinkedList<ProofDisposedListener>();
    
    /** constructs a new empty proof with name */
    private Proof(Name name, InitConfig initConfig, ProofSettings settings) {
        this.name = name;
        assert initConfig != null : "Tried to create proof without valid services.";
	     this.initConfig = initConfig;
	     
	     this.initConfig.getServices().setProof(this);
	     
        settingsListener =
                new SettingsListener () {
                    @Override
                    public void settingsChanged ( GUIEvent config ) {
                        updateStrategyOnGoals();
                    }
                };
                        
        localMgt = new ProofCorrectnessMgt(this);

        setSettings(settings);
        pis = ProofIndependentSettings.DEFAULT_INSTANCE;
    }

    /**
     * initialises the strategies
     */
    private void initStrategy() {
        StrategyProperties activeStrategyProperties =
            settings.getStrategySettings().getActiveStrategyProperties();

        final Profile profile = getServices().getProfile();

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
    public Proof(InitConfig initConfig) {
	this ( "", initConfig );
    }


    /** constructs a new empty proof with name */
    public Proof(String name, InitConfig initConfig) {
	this ( new Name ( name ),
	      initConfig,
               new ProofSettings ( ProofSettings.DEFAULT_SETTINGS ) );
    }

    private Proof(String name, Sequent problem, TacletIndex rules,
            BuiltInRuleIndex builtInRules, InitConfig initConfig,
            ProofSettings settings) {

        this ( new Name ( name ), initConfig, settings );

	localMgt = new ProofCorrectnessMgt(this);

        Node rootNode = new Node(this, problem);
        setRoot(rootNode);

	Goal firstGoal = new Goal(rootNode,
                                  new RuleAppIndex(new TacletAppIndex(rules, getServices()),
						   new BuiltInRuleAppIndex(builtInRules), getServices()));
	openGoals = openGoals.prepend(firstGoal);

	if (closed())
	    fireProofClosed();
    }

    public Proof(String name, Term problem, String header, TacletIndex rules,
         BuiltInRuleIndex builtInRules, InitConfig initConfig, ProofSettings settings) {
        this ( name, Sequent.createSuccSequent
                 (Semisequent.EMPTY_SEMISEQUENT.insert(0,
                         new SequentFormula(problem)).semisequent()),
                 rules, builtInRules, initConfig, settings );
        problemHeader = header;
    }


    public Proof(String name, Sequent sequent, String header, TacletIndex rules,
            BuiltInRuleIndex builtInRules, InitConfig initConfig, ProofSettings settings) {
        this ( name, sequent, rules, builtInRules, initConfig, settings );
        problemHeader = header;
    }


    public Proof (String name,
                  Term problem,
                  String header,
                  TacletIndex rules,
                  BuiltInRuleIndex builtInRules,
                  InitConfig initConfig) {
        this ( name,
               problem,
               header,
               rules,
               builtInRules,
               initConfig,
               new ProofSettings ( ProofSettings.DEFAULT_SETTINGS ) );
    }


    /**
     * Cut off all reference such that it does not lead to a big memory leak
     * if someone still holds a refernce to this proof object.
     */
    public void dispose() {
        // Do required cleanup
        if (getServices() != null) {
           getServices().getSpecificationRepository().removeProof(this);
        }
        if (localMgt != null) {
           localMgt.removeProofListener(); // This is strongly required because the listener is contained in a static List
        }
        // remove setting listener from settings
        setSettings(null);
        // set every reference (except the name) to null
        root = null;        
        env = null;
        openGoals = null;
        problemHeader = null;
        abbreviations = null;
        initConfig = null;
        localMgt = null;
        settings = null;
        userLog = null;
        keyVersionLog = null;
        activeStrategy = null;
        settingsListener = null;
        disposed = true;
        ruleAppListenerList = null;
        listenerList = null;
        fireProofDisposed(new ProofDisposedEvent(this));
    }


    /**
     * Returns true if the proof has been abandoned and the dispose method has
     * been called on this object. Should be asserted before proof object is
     * accessed.
     */
    public boolean isDisposed() {
        return disposed;
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
       return initConfig.getServices();
    }

    public long getAutoModeTime() {
        return autoModeTime;
    }

    public void addAutoModeTime(long time) {
        autoModeTime += time;
    }



    /** sets the variable, function, sort, heuristics namespaces */
    public void setNamespaces(NamespaceSet ns) {
        getServices().setNamespaces(ns);
        if (openGoals().size() > 1)
            throw new IllegalStateException("Proof: ProgVars set too late");
        openGoals().head().setProgramVariables(ns.programVariables());
    }

    public ProofEnvironment getEnv() {
       return env;
    }

    public void setEnv(ProofEnvironment env) {
       this.env = env;
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

        final Iterator<Goal> it = openGoals ().iterator ();
        while ( it.hasNext () )
            it.next ().setGoalStrategy(ourStrategy);
    }


    public void clearAndDetachRuleAppIndexes () {
        // Taclet indices of the particular goals have to
        // be rebuilt
        final Iterator<Goal> it = openGoals ().iterator ();
        while ( it.hasNext () )
            it.next ().clearAndDetachRuleAppIndex ();
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


    public final void setSettings(ProofSettings newSettings) {
        if (settings != null ){
            // deregister settings listener
            settings.getStrategySettings().removeSettingsListener(settingsListener);
        }
        settings = newSettings;
        if (settings != null ){
            // register settings listener
            settings.getStrategySettings().addSettingsListener (settingsListener);
        }
    }


    public ProofSettings getSettings() {
        return settings;
    }
    public ProofIndependentSettings getProofIndependentSettings(){
    	return pis;
    }

    /**
     * returns the list of open goals
     * @return list with the open goals
     */
    public ImmutableList<Goal> openGoals() {
	return openGoals;
    }


    /**
     * return the list of open and enabled goals
     * @return list of open and enabled goals, never null
     * @author mulbrich
     */
    public ImmutableList<Goal> openEnabledGoals() {
        return filterEnabledGoals(openGoals);
    }


    /**
     * filter those goals from a list which are enabled
     *
     * @param goals non-null list of goals
     * @return sublist such that every goal in the list is enabled
     * @see Goal#isAutomatic()
     * @author mulbrich
     */
    private ImmutableList<Goal> filterEnabledGoals(ImmutableList<Goal> goals) {
        ImmutableList<Goal> enabledGoals = ImmutableSLList.<Goal>nil();
        for(Goal g : goals) {
            if(g.isAutomatic()) {
                enabledGoals = enabledGoals.prepend(g);
            }
        }
        return enabledGoals;
    }


    /**
     * removes the given goal and adds the new goals in list
     * @param oldGoal the old goal that has to be removed from list
     * @param newGoals the IList<Goal> with the new goals that were
     * result of a rule application on goal
     */
    public void replace(Goal oldGoal, ImmutableList<Goal> newGoals) {
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
    public void closeGoal ( Goal p_goal ) {

	Node closedSubtree = p_goal.node().close();

	boolean        b    = false;
	Iterator<Node> it   = closedSubtree.leavesIterator ();
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
	    fireProofGoalsAdded ( ImmutableSLList.<Goal>nil() );
    }

    /** removes the given goal from the list of open goals. Take care
     * removing the last goal will fire the proofClosed event
     * @param goal the Goal to be removed
     */
    private void remove(Goal goal) {
	ImmutableList<Goal> newOpenGoals = openGoals.removeAll(goal);
	if (newOpenGoals != openGoals) {
	    openGoals = newOpenGoals;
	    if (closed()) {
		fireProofClosed();
	    } else {
		fireProofGoalRemoved(goal);
	    }
	}
    }

    /** for testing only */
    @Deprecated
    void remove2(Goal goal){
        remove(goal);
    }


    /** adds a new goal to the list of goals
     * @param goal the Goal to be added
     */
    public void add(Goal goal) {
	ImmutableList<Goal> newOpenGoals = openGoals.prepend(goal);
	if (openGoals != newOpenGoals) {
	    openGoals = newOpenGoals;
	    fireProofGoalsAdded(goal);
	}
    }


    /** adds a list with new goals to the list of open goals
     * @param goals the IList<Goal> to be prepended
     */
    public void add(ImmutableList<Goal> goals) {
	ImmutableList<Goal> newOpenGoals = openGoals.prepend(goals);
	if (openGoals != newOpenGoals) {
	    openGoals = newOpenGoals;
	}

	// For the moment it is necessary to fire the message ALWAYS
	// in order to detect branch closing.
	fireProofGoalsAdded(goals);

    }


    /**
     * returns true if the root node is marked as closed and all goals have been removed
     */
    public boolean closed () {
	return root.isClosed() && openGoals.isEmpty();
    }





    /**
     * This class is responsible for pruning a proof tree at a certain cutting point.
     * It has been introduced to encapsulate the methods that are needed for pruning.
     * Since the class has influence on the internal state of the proof it should not be
     * moved to a new file, in order to restrict the access to it.
     */
    private class ProofPruner{
            private Node firstLeaf = null;

            public ImmutableList<Node> prune(final Node cuttingPoint){

                  // there is only one leaf containing a open goal that is interesting for pruning the sub-tree of <code>node</code>,
                  // namely the first leave that is found by a breadth first search.
                  // The other leaves containing open goals are only important for removing the open goals from the open goal list.
                  // To that end those leaves are stored in residualLeaves. For increasing the performance a tree structure has been
                  // chosen, because it offers the operation <code>contains</code> in O(log n).
                  final Set<Node> residualLeaves = new TreeSet<Node>(new Comparator<Node>() {
                        @Override
                        public int compare(Node o1, Node o2) {
                                return o1.serialNr()-o2.serialNr();
                        }
                  });


                  // First, make a breadth first search, in order to find the leaf with the shortest distance to the cutting point
                  // and to remove the rule applications from the proof management system.
                  // Furthermore store the residual leaves.
                  breadthFirstSearch(cuttingPoint, new ProofVisitor() {
                        @Override
                        public void visit(Proof proof, Node visitedNode) {
                                if(visitedNode.leaf() && !visitedNode.isClosed()){
                                        if(firstLeaf == null){
                                                firstLeaf = visitedNode;
                                        }else{
                                                residualLeaves.add(visitedNode);
                                        }

                                }

                                if (initConfig != null && visitedNode.parent() != null) {
                                        	Proof.this.mgt().ruleUnApplied(visitedNode.parent().getAppliedRuleApp());
                                          for (final NoPosTacletApp app :  visitedNode.parent().getLocalIntroducedRules()){
                                             initConfig.getJustifInfo().removeJustificationFor(app.taclet());
                                         }

                                }

                        }
                  });

                  final Goal firstGoal = getGoal(firstLeaf);
                  assert firstGoal != null;

                  // Go from the first leaf that has been found to the cutting point. For each node on the path remove
                  // the local rules from firstGoal that have been added by the considered node.
                  traverseFromChildToParent(firstLeaf,cuttingPoint,new ProofVisitor() {

                        @Override
                        public void visit(Proof proof, Node visitedNode) {
                            for (final NoPosTacletApp app :  visitedNode.getLocalIntroducedRules()){
                                firstGoal.ruleAppIndex().removeNoPosTacletApp(app);
                                initConfig.getJustifInfo().removeJustificationFor(app.taclet());
                            }

                            firstGoal.pruneToParent();
                        }
                  });

                  // do some cleaning and refreshing: Clearing indices, caches....
                  refreshGoal(firstGoal,cuttingPoint);

                  // cut the subtree, it is not needed anymore.
                  ImmutableList<Node> subtrees =cut(cuttingPoint);


                  //remove the goals of the residual leaves.
                  removeOpenGoals(residualLeaves);
                  return subtrees;

            }

            private void refreshGoal(Goal goal, Node node){
                    goal.setGlobalProgVars(node.getGlobalProgVars());
                    goal.getRuleAppManager().clearCache();
                    goal.ruleAppIndex().clearIndexes();
                    goal.node().setAppliedRuleApp(null);
                    node.clearNameCache();
            }

            private void removeOpenGoals(Collection<Node> toBeRemoved){
                    ImmutableList<Goal> newGoalList = ImmutableSLList.nil();
                    for(Goal openGoal : openGoals){
                          if(!toBeRemoved.contains(openGoal.node())){
                                  newGoalList = newGoalList.append(openGoal);
                          }
                    }
                    openGoals = newGoalList;
            }


            private ImmutableList<Node> cut(Node node){
                    ImmutableList<Node> children = ImmutableSLList.nil();
                    Iterator<Node> it = node.childrenIterator();

                    while(it.hasNext()) {
                            children = children.append(it.next());

                    }
                    for(Node child : children){
                            node.remove(child);
                    }
                    return children;
            }

    }

    public void pruneProof(Goal goal){
            if(goal.node().parent()!= null){
                    pruneProof(goal.node().parent());
            }
    }

    /**
     * Prunes the subtree beneath the node <code>cuttingPoint</code>, i.e. the node
     * <code>cuttingPoint</code> remains as the last node on the branch. As a result a
     * open goal is associated with this node.
     * @param cuttingPoint
     * @return Returns the sub trees that has been pruned.
     */

    public ImmutableList<Node> pruneProof(Node cuttingPoint){
        return pruneProof(cuttingPoint,true);
    }

    public ImmutableList<Node> pruneProof(Node cuttingPoint,boolean fireChanges){
        assert cuttingPoint.proof() == this;
        if(getGoal(cuttingPoint)!= null || cuttingPoint.isClosed()){
                return null;
        }

        ProofPruner pruner = new ProofPruner();
        if(fireChanges){
            fireProofIsBeingPruned(cuttingPoint);
        }
        ImmutableList<Node> result = pruner.prune(cuttingPoint);
        if(fireChanges){
            fireProofGoalsChanged();
            fireProofPruned(cuttingPoint);
        }
        return result;
    }

    /**
     * Makes a downwards directed breadth first search on the proof tree, starting with node
     *  <code>startNode</code>. The visited notes are reported to the object <code>visitor</code>.
     *  The first reported node is <code>startNode</code>.
     */
    public void breadthFirstSearch(Node startNode, ProofVisitor visitor){
            ArrayDeque<Node> queue = new ArrayDeque<Node>();
            queue.add(startNode);
            while(!queue.isEmpty()){
                    Node currentNode = queue.poll();
                    Iterator<Node> it = currentNode.childrenIterator();
                    while(it.hasNext()){
                            queue.add(it.next());
                    }
                    visitor.visit(this, currentNode);
            }
    }

    public void traverseFromChildToParent(Node child, Node parent, ProofVisitor visitor){
            do{
                visitor.visit(this, child);
                child = child.parent();
            }while(child != parent);
    }






    /** fires the event that the proof has been expanded at the given node */
    public void fireProofExpanded(Node node) {
	ProofTreeEvent e = new ProofTreeEvent(this, node);
    for (ProofTreeListener listener : listenerList) {
	    listener.proofExpanded(e);
	}
    }


    /** fires the event that the proof has been pruned at the given node */
    protected void fireProofIsBeingPruned(Node below) {
        ProofTreeEvent e = new ProofTreeEvent(this, below);
        for (ProofTreeListener listener : listenerList) {
            listener.proofIsBeingPruned(e);
        }
    }


    /** fires the event that the proof has been pruned at the given node */
    protected void fireProofPruned(Node below) {
	ProofTreeEvent e = new ProofTreeEvent(this, below);
    for (ProofTreeListener listener : listenerList) {
        listener.proofPruned(e);
	}
    }


    /** fires the event that the proof has been restructured */
    public void fireProofStructureChanged() {
	ProofTreeEvent e = new ProofTreeEvent(this);
    for (ProofTreeListener listener : listenerList) {
	    listener.proofStructureChanged(e);
	}
    }


    /** fires the event that a goal has been removed from the list of goals */
    protected void fireProofGoalRemoved(Goal goal) {
	ProofTreeEvent e = new ProofTreeEvent(this, goal);
    for (ProofTreeListener listener : listenerList) {
	    listener.proofGoalRemoved(e);
	}
    }


    /** fires the event that new goals have been added to the list of
     * goals
     */
    protected void fireProofGoalsAdded(ImmutableList<Goal> goals) {
	ProofTreeEvent e = new ProofTreeEvent(this, goals);
    for (ProofTreeListener listener : listenerList) {
	    listener.proofGoalsAdded(e);
	}
    }


    /** fires the event that new goals have been added to the list of
     * goals
     */
    protected void fireProofGoalsAdded(Goal goal) {
	fireProofGoalsAdded(ImmutableSLList.<Goal>nil().prepend(goal));
    }


    /** fires the event that the proof has been restructured */
    public void fireProofGoalsChanged() {
	ProofTreeEvent e = new ProofTreeEvent(this, openGoals());
	for (ProofTreeListener listener : listenerList) {
	    listener.proofGoalsChanged(e);
	}
    }


    /** fires the event that the proof has closed.
     * This event fired instead of the proofGoalRemoved event when
     * the last goal in list is removed.
     */
    protected void fireProofClosed() {
	ProofTreeEvent e = new ProofTreeEvent(this);
    for (ProofTreeListener listener : listenerList) {
	    listener.proofClosed(e);
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
       if (listenerList != null) {
          synchronized(listenerList) {
             listenerList.remove(listener);
         }
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
	for (final Goal result : openGoals) {
	    if (result.node() == node) {
		return result;
	    }
	}
	return null;
    }


    /** returns the list of goals of the subtree starting with node
     *
     * @param node the Node where to start from
     * @return the list of goals of the subtree starting with node
     */
    public ImmutableList<Goal> getSubtreeGoals(Node node) {
	ImmutableList<Goal> result = ImmutableSLList.<Goal>nil();
	for (final Goal goal : openGoals) {
	    final Iterator<Node> leavesIt = node.leavesIterator();
	    while (leavesIt.hasNext()) {
		if (leavesIt.next() == goal.node()) {
		    result = result.prepend(goal);
		}
	    }
	}
	return result;
    }

    /**
     * get the list of goals of the subtree starting with node which are enabled.
     * @param node the Node where to start from
     * @return the list of enabled goals of the subtree starting with node
     */
    public ImmutableList<Goal> getSubtreeEnabledGoals(Node node) {
        return filterEnabledGoals(getSubtreeGoals(node));
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
    for (final Goal g : openGoals) {
	    g.ruleAppIndex ().autoModeStarted ();
	}
    }


    public void setRuleAppIndexToInteractiveMode () {
	for (final Goal g : openGoals) {
	    g.ruleAppIndex ().autoModeStopped ();
	}
    }


    /**
     * retrieves number of branches
     */
    public int countBranches() {
        return root.countBranches();
    }


    /** Retrieves a bunch of statistics to the proof tree.
     * This implementation traverses the proof tree only once.
     * Statistics are not cached; don't call this method too often.
     */
    public Statistics statistics() {
        return new Statistics(this);
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

    /**
     * Instances of this class encapsulate statistical information about proofs,
     * such as the number of nodes, or the number of interactions.
     * @author bruns
     *
     */
    public final static class Statistics {
        public final int nodes;
        public final int branches;
        public final int interactiveSteps;
        public final int quantifierInstantiations;
        public final int ossApps;
        public final int totalRuleApps;
        public final int smtSolverApps;
        public final int dependencyContractApps;
        public final int operationContractApps;
        public final int loopInvApps;
        public final long autoModeTime;
        public final long time;
        public final float timePerStep;

        private List<Pair<String, String>> summaryList =
                new ArrayList<Pair<String, String>>(14);


        private Statistics(Proof proof) {
            final Iterator<Node> it = proof.root().subtreeIterator();

            int tmpNodes = 0; // proof nodes
            int tmpBranches = 1; // proof branches
            int tmpInteractive = 0; // interactive steps
            int tmpQuant = 0; // quantifier instantiations
            int tmpOss = 0; // OSS applications
            int tmpOssCaptured = 0; // rules apps in OSS protocol
            int tmpSmt = 0; // SMT rule apps
            int tmpDep = 0; // dependency contract apps
            int tmpContr = 0; // functional contract apps
            int tmpInv = 0; // loop invariants

            while (it.hasNext()) {
                tmpNodes++;
                final Node node = it.next();
                final int c = node.childrenCount();
                if (c > 1) {
                    tmpBranches += c - 1;
                }

                if (node.getNodeInfo().getInteractiveRuleApplication()) {
                    tmpInteractive++;
                }

                final RuleApp ruleApp = node.getAppliedRuleApp();
                if (ruleApp != null) {

                    if (ruleApp instanceof de.uka.ilkd.key.rule.OneStepSimplifierRuleApp) {
                        tmpOss++;
                        final Protocol protocol =
                                ((de.uka.ilkd.key.rule.OneStepSimplifierRuleApp) ruleApp).getProtocol();
                        if (protocol != null) {
                            tmpOssCaptured += protocol.size() - 1;
                        }
                    } else if (ruleApp instanceof de.uka.ilkd.key.smt.RuleAppSMT) {
                        tmpSmt++;
                    } else if (ruleApp instanceof UseDependencyContractApp) {
                        tmpDep++;
                    } else if (ruleApp instanceof ContractRuleApp) {
                        tmpContr++;
                    } else if (ruleApp instanceof LoopInvariantBuiltInRuleApp) {
                        tmpInv++;
                    } else if (ruleApp instanceof TacletApp) {
                        final de.uka.ilkd.key.rule.Taclet t = ((TacletApp)ruleApp).taclet();
                        final String tName = t.name().toString();
                        if (tName.startsWith("allLeft") || tName.startsWith("exRight") || tName.startsWith("inst")) {
                            tmpQuant++;
                        }
                    }
                }
            }

            this.nodes = tmpNodes;
            this.branches = tmpBranches;
            this.interactiveSteps = tmpInteractive;
            this.quantifierInstantiations = tmpQuant;
            this.ossApps = tmpOss;
            this.totalRuleApps = tmpNodes + tmpOssCaptured;
            this.smtSolverApps = tmpSmt;
            this.dependencyContractApps = tmpDep;
            this.operationContractApps = tmpContr;
            this.loopInvApps = tmpInv;
            this.autoModeTime = proof.getAutoModeTime();
            this.time = System.currentTimeMillis() - Main.getStartTime();
            timePerStep = autoModeTime/(float)nodes;

            generateSummary(proof);
        }

        private void generateSummary(Proof proof) {
            final String nodeString =
                    EnhancedStringBuffer.format(nodes).toString();
            summaryList.add(new Pair<String, String>("Nodes", nodeString));
            summaryList.add(new Pair<String, String>("Branches",
                                                     EnhancedStringBuffer.format(branches).toString()));
            summaryList.add(new Pair<String, String>("Interactive steps", "" +
                                                                          interactiveSteps));
            final long time = proof.getAutoModeTime();
            summaryList.add(new Pair<String, String>("Automode time",
                                                     EnhancedStringBuffer.formatTime(time).toString()));
            if (time >= 10000) {
                summaryList.add(new Pair<String, String>("Automode time", "" +
                                                                          time +
                                                                          "ms"));
            }
            if (nodes > 0) {
                String avgTime = "" + timePerStep;
                // round to 3 digits after point
                int i = avgTime.indexOf('.')+4;
                if (i > avgTime.length()) i = avgTime.length();
                avgTime = avgTime.substring(0,i);
                summaryList.add(new Pair<String, String>("Avg. time per step", "" +
                                                                               avgTime +
                                                                               "ms"));
            }

            summaryList.add(new Pair<String, String>("Rule applications", ""));
            summaryList.add(new Pair<String, String>("Quantifier instantiations", ""+quantifierInstantiations));
            summaryList.add(new Pair<String, String>("One-step Simplifier apps", "" +
                                                                                 ossApps));
            summaryList.add(new Pair<String, String>("SMT solver apps", "" +
                                                                        smtSolverApps));
            summaryList.add(new Pair<String, String>("Dependency Contract apps", "" +
                                                                                 dependencyContractApps));
            summaryList.add(new Pair<String, String>("Operation Contract apps", "" +
                                                                                operationContractApps));
            summaryList.add(new Pair<String, String>("Loop invariant apps", "" +
                                                                            loopInvApps));
            summaryList.add(new Pair<String, String>("Total rule apps",
                                                     EnhancedStringBuffer.format(totalRuleApps).toString()));
        }


        public List<Pair<String, String>> getSummary() {
            return summaryList;
        }

        @Override
        public String toString() {
            StringBuffer sb = new StringBuffer("Proof Statistics:\n");
            for (Pair<String,String> p: summaryList) {
                final String c = p.first;
                final String s = p.second;
                sb = sb.append(c);
                if (!"".equals(s)) {
                    sb = sb.append(": ").append(s);
                }
                sb = sb.append('\n');
            }
            sb.deleteCharAt(sb.length()-1);
            return sb.toString();
        }
    }
    

   /** fires the event that a rule has been applied */
   protected void fireRuleApplied(ProofEvent p_e) {
      synchronized (ruleAppListenerList) {
         for (RuleAppListener ral : ruleAppListenerList) {
            ral.ruleApplied(p_e);
         }
      }
   }

   public void addRuleAppListener(RuleAppListener p) {
      synchronized (ruleAppListenerList) {
         ruleAppListenerList.add(p);
      }
   }

   public void removeRuleAppListener(RuleAppListener p) {
      synchronized (ruleAppListenerList) {
         ruleAppListenerList.remove(p);
      }
   }
   
   /**
    * Registers the given {@link ProofDisposedListener}.
    * @param l The {@link ProofDisposedListener} to register.
    */
   public void addProofDisposedListener(ProofDisposedListener l) {
      if (l != null) {
         proofDisposedListener.add(l);
      }
   }
   
   /**
    * Unregisters the given {@link ProofDisposedListener}.
    * @param l The {@link ProofDisposedListener} to unregister.
    */
   public void removeProofDisposedListener(ProofDisposedListener l) {
      if (l != null) {
         proofDisposedListener.remove(l);
      }
   }
   
   /**
    * Returns all registered {@link ProofDisposedListener}.
    * @return All registered {@link ProofDisposedListener}.
    */
   public ProofDisposedListener[] getProofDisposedListeners() {
      return proofDisposedListener.toArray(new ProofDisposedListener[proofDisposedListener.size()]);
   }
   
   /**
    * Fires the event {@link ProofDisposedListener#proofDisposed(ProofDisposedEvent)} to all listener.
    * @param e The event to fire.
    */
   protected void fireProofDisposed(ProofDisposedEvent e) {
      ProofDisposedListener[] listener = getProofDisposedListeners();
      for (ProofDisposedListener l : listener) {
         l.proofDisposed(e);
      }
   }

   public InitConfig getInitConfig() {
      return initConfig;
   }

}