// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.delayedcut;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
    
/**
 * This class is responsible for processing the delayed cut. The information about the cut 
 * is stored in  <code>DelayCut</code>. For each cut a new object of this class must be created.
 * The cutting process consists of three steps:
 * 1. The proof tree is pruned to the node the process is applied on. For step 3 the tree is stored. 
 * 2. The taclet 'cut' is applied on the resulting goal of step 1 using the formula F that is specified when calling 
 * the constructor. (The formula is called decision predicate). In one goal the decision predicate occurs in the antecedent
 * and in the other in the succedent. 
 * 3. The pruned subtree is attached to one of both goals. Hence, there are two possible modes:
 * <code>DECISION_PREDICATE_IN_ANTECEDENT</code>: The pruned subtree is attached to the goal having F in its antecedent.
 * <code>DECISION_PREDICATE_IN_SUCCEDENT</code>: The pruned subtree is attached to the goal having F in its succedent.
 * Let G be the goal the pruned subtree is attached to:
 * 3.1 F is hidden in G.
 * 3.2 The pruned subtree is rebuilt by applying the rules of the subtree on G: The proof represented by the subtree is 
 * replayed. 
 * 3.3. F is uncovered in G.
 * Remark: F must not exist already in the sequent the process is applied on. Since a antecedent respective succedent is a set of 
 * formulas the hiding mechanism of F does not work. An already existing formula would be hidden.  
 * 
 * REMARK: Before you change this class, see the comment at the method <code>apply</code>.
 */
public class DelayedCutProcessor implements Runnable {
     
    /**
     * The names of the taclets used by the process.
     */
    private static final String HIDE_RIGHT_TACLET = "hide_right";
    private static final String HIDE_LEFT_TACLET  = "hide_left";
    private static final String CUT_TACLET = "cut";
    private static final int DEC_PRED_INDEX = 0;

    private final LinkedList<DelayedCutListener> listeners = new LinkedList<DelayedCutListener>();
    private final Proof proof;
    private final Node  node;
    private final Term  descisionPredicate;
    private final int   mode;
    private boolean     used = false;
    
    

    
    public void add(DelayedCutListener listener){
        listeners.add(listener);
    }
    
    public void remove(DelayedCutListener listener){
        listeners.remove(listener);
    }

    public static List<ApplicationCheck> getApplicationChecks(){
    	List<ApplicationCheck> list = new LinkedList<ApplicationCheck>();
    	list.add(new ApplicationCheck.NoNewSymbolsCheck());
    	return list;
    }
    
    
    public DelayedCutProcessor(Proof proof, Node node, Term descisionPredicate,
            int mode) {
        super();
        this.proof = proof;
        this.node = node;
        this.descisionPredicate = descisionPredicate;
        this.mode = mode;
    }

    private Goal find(Proof proof, Node node){
        for(Goal goal : proof.openGoals()){
            if(goal.node() == node){
                return goal;
            }
        }
        return null;
    }
    
    public DelayedCut cut(){
        if(used){
            throw new IllegalStateException("For each cut a new object of this class must be created.");
        }
        used = true;
        for(DelayedCutListener listener : listeners){
            listener.eventCutting();
        }
         // do not change the order of the following two statements!
         RuleApp firstAppliedRuleApp = node.getAppliedRuleApp(); 
         ImmutableList<Node> subtrees = proof.pruneProof(node,false);
         
         
         DelayedCut delayedCut = new DelayedCut(proof, node,
                                                descisionPredicate, subtrees,
                                                mode,firstAppliedRuleApp);
         
         // apply the cut rule on the node.
         ImmutableList<Goal> result = cut(delayedCut);      

         // hide the decision predicate.
         int indexForHiding = getGoalForHiding(result, delayedCut);
         Goal hide = indexForHiding == 0 ? result.head() :
                                result.tail().head();
         delayedCut.setRemainingGoal(indexForHiding == 1 ? result.head() :
                                result.tail().head());
         
         result = hide(delayedCut,hide);
                  
         // rebuild the tree that has been pruned before.
         List<NodeGoalPair> openLeaves = rebuildSubTrees(delayedCut, result.head());
     
         // uncover the decision predicate.
         uncoverDecisionPredicate(delayedCut, openLeaves);
     
         for(DelayedCutListener listener : listeners){
             listener.eventEnd(delayedCut);
         }     
   
         return delayedCut;
    }
    

    
   
    
    
    
    
    private ImmutableList<Goal> cut(DelayedCut cut){
        Goal goal = find(cut.getProof(), cut.getNode());

        TacletFilter filter = new TacletFilter() {
            
            @Override
            protected boolean filter(Taclet taclet) {
                
                return taclet.name().toString().equals(CUT_TACLET);
            }
            
            
        };
        
        ImmutableList<NoPosTacletApp> apps =  goal.ruleAppIndex().getNoFindTaclet(filter, cut.getServices());
        assert apps.size() == 1;
         
        TacletApp app = apps.head();
        
        app = app.addCheckedInstantiation(app.uninstantiatedVars().iterator().next(),
                                    cut.getFormula(),cut.getServices(), true);
        return goal.apply(app);
    }
    
    private ImmutableList<Goal> apply(final String tacletName,Goal goal, PosInOccurrence pio){
        TacletFilter filter = new TacletFilter() {
            
            @Override
            protected boolean filter(Taclet taclet) {
                
                return taclet.name().toString().equals(tacletName);
            }
            
            
        };
     
        ImmutableList<NoPosTacletApp> apps =  goal.ruleAppIndex().getFindTaclet(filter,pio,goal.proof().getServices());
        assert apps.size() == 1;
        NoPosTacletApp app = apps.head();
        
        PosTacletApp app2 = app.setPosInOccurrence(pio, goal.proof().getServices());
        return goal.apply(app2); 
    }
    
    /**
     * Hides the formula that has been added by the hide process.*/
    private ImmutableList<Goal> hide(DelayedCut cut, Goal goal){
  
        SequentFormula sf = getSequentFormula(goal, cut.isDecisionPredicateInAntecendet());
        
        
        PosInOccurrence pio = new PosInOccurrence(sf,PosInTerm.TOP_LEVEL,
                cut.isDecisionPredicateInAntecendet());
        
        ImmutableList<Goal> result= apply(getHideTacletName(cut), goal, pio);
          cut.setHideApp(result.head().node().getLocalIntroducedRules().iterator().next());
        return result;
    }
    
    /**
     * After applying the cut rule two goal result. The pruned subtree is added to one of these goals. 
     * This method finds the the goal.
     *     */
    private int getGoalForHiding(ImmutableList<Goal> goals, DelayedCut cut){
        assert goals.size() == 2;
        Goal [] goal = {goals.head(),goals.tail().head()};
       
          
        for(int i=0; i < 2; i++){
             String side = cut.isDecisionPredicateInAntecendet() 
                     ? "TRUE":"FALSE";
           
            if(goal[i].node().getNodeInfo().getBranchLabel().endsWith(side)){
                SequentFormula formula = getSequentFormula(goal[i], cut.isDecisionPredicateInAntecendet());
                if(formula.formula() == cut.getFormula()){
                    return i;
                }
            }
        }
        throw new IllegalStateException("After a cut a goal belongs to the left or right side of the tree");
    }
    

    
    private String getHideTacletName(DelayedCut cut){
        return cut.isDecisionPredicateInAntecendet() ?HIDE_LEFT_TACLET:
            HIDE_RIGHT_TACLET;        
    }
    
    
    private SequentFormula getSequentFormula(Goal goal, boolean decPredInAnte){
        return decPredInAnte ?
                goal.sequent().antecedent().get(DEC_PRED_INDEX): 
                    goal.sequent().succedent().get(DEC_PRED_INDEX);
        
    }
    
    /**
     * Rebuilds the subtree pruned by the process, that is the rules are replayed. 
     *  */
    private List<NodeGoalPair> rebuildSubTrees(DelayedCut cut, Goal goal){
        LinkedList<NodeGoalPair> pairs = new LinkedList<NodeGoalPair>();
        LinkedList<NodeGoalPair>  openLeaves = new LinkedList<NodeGoalPair>();
 
        add(pairs,openLeaves,cut.getSubtrees().iterator(),
        		  apply(cut.getNode(),goal,cut.getFirstAppliedRuleApp(),cut.getServices()));

        int totalNumber = 0;
        for(NodeGoalPair pair : pairs){
            totalNumber += pair.node.countNodes();
        }

        int currentNumber =0;
        while(!pairs.isEmpty()){
            
            NodeGoalPair pair = pairs.pollLast();

            RuleApp app = createNewRuleApp(pair,
                    cut.getServices());
         
     
           
            totalNumber -= add(pairs,openLeaves,pair.node.childrenIterator(),
                   apply(pair.node,pair.goal,app,cut.getServices()));
          

            for(DelayedCutListener listener : listeners){
                listener.eventRebuildingTree(++currentNumber, totalNumber);
            }
        }
        return openLeaves;
    }
    
    /**
     * CAUTION: The order of the goals is crucial for the success of the delayed cut. Since the method 
     * Goal::split() prepends goals to the current list. If you have some problems with the delayed cut, 
     * have a look the Goal::split(), whether this has changed. 
     * Up to now the order must therefore reversed, otherwise if the proof splits up into several branches
     * the rules are applied on the wrong nodes which results in exceptions.  
     * 
     * @param goal
     * @param app
     * @return
     */
    private LinkedList<Goal> apply(Goal goal, RuleApp app, Services services){
        if(app instanceof TacletApp){
        	TacletApp tapp = (TacletApp) app;
        	final SVInstantiations insts = tapp.instantiations();
        	final Iterator<SchemaVariable> svIt = insts.svIterator();
        	while(svIt.hasNext()) {
        	    final SchemaVariable sv = svIt.next();
        	    if(sv instanceof SkolemTermSV) {
        		final Term inst = (Term) insts.getInstantiation(sv);
        		   		 services.getNamespaces().functions().remove(inst.op().name());
        	    }
        	}
        }

    	
        LinkedList<Goal> goals = new LinkedList<Goal>();
        ImmutableList<Goal> childs =  goal.apply(app);
        

        // if the rule is a SMT rule, <code>childs</code> can be null.
        //if(childs == null){
        //	return goals;
        //}
        for(Goal child : childs){
        	goals.addFirst(child);
        }
        return goals;
    }
    
    private LinkedList<Goal> apply(Node oldNode, Goal goal, RuleApp app, Services services){
    	 try{
    		return apply(goal, app, services);
    	}catch(Throwable e){
    		throw new RuntimeException("Problem with replaying node "+oldNode.serialNr(), e);
    	}
    }
    
    /**
     * Based on an old rule application a new rule application is built. Mainly 
     * the position is updated.
     */
    private RuleApp createNewRuleApp(NodeGoalPair pair, Services services){
        RuleApp oldRuleApp = pair.node.getAppliedRuleApp();
        
        
        PosInOccurrence newPos = translate(pair,services);
        try{
        check(pair.goal,oldRuleApp,newPos,services);
        }catch(Throwable e){
        	throw new RuntimeException("Problem with replaying node " + pair.node.serialNr(),e);
        }

        if(oldRuleApp instanceof PosTacletApp){
            PosTacletApp app = (PosTacletApp) oldRuleApp; 
            return PosTacletApp.createPosTacletApp((FindTaclet)app.taclet(),
                    app.instantiations(),app.ifFormulaInstantiations(),
                    newPos
                    ,services);
        }

        if(oldRuleApp instanceof IBuiltInRuleApp){
            IBuiltInRuleApp app = (IBuiltInRuleApp) oldRuleApp;
            return app.replacePos(newPos);
        }
        
        return oldRuleApp;
        
    }
    
    private void check(Goal goal,final RuleApp app, PosInOccurrence newPos, Services services){
        if(newPos == null){
            return;
        }
    	if(app instanceof IBuiltInRuleApp){
    		BuiltInRule rule = (BuiltInRule) app.rule();
    		if(rule.isApplicable(goal, newPos)){
    			return;
    		}
//    		for(RuleApp newApp: goal.ruleAppIndex().getBuiltInRules(goal, newPos)){
//    			if(app.rule().name().compareTo(newApp.rule().name()) == 0){
//    				return;
//    			}    			
//    		}
//  
    		throw new RuntimeException("Cannot apply built-in rule-app");
    		
    	}
    	
    	if(app instanceof TacletApp){
    		NoPosTacletApp noPosApp = NoPosTacletApp.createNoPosTacletApp((Taclet)app.rule());
    		if(noPosApp.matchFind(newPos, services) == null){

        		throw new RuntimeException("Cannot apply taclet-app");
    		}
    		return;
//    		ImmutableList<TacletApp> list = goal.ruleAppIndex().getTacletAppAt(new TacletFilter() {
//			
//			@Override
//			protected boolean filter(Taclet taclet) {			
//				return taclet.name().compareTo(app.rule().name()) == 0;
//			}
//    		}, newPos, services);
//    
//    	    if(!list.isEmpty()){
//    	    	return;
//    	    }
//
//    		throw new RuntimeException("Cannot apply taclet-app");
    	}
    	
    	throw new RuntimeException("App is neither a BuiltInApp nor a TacletApp, it's  of type"+app.getClass().getName());
    	
    }
    
    
    private PosInOccurrence translate(NodeGoalPair pair,Services services){
        RuleApp oldRuleApp = pair.node.getAppliedRuleApp();
        if(oldRuleApp == null ||oldRuleApp.posInOccurrence() == null){
            return null;
        }
        int formulaNumber = pair.node.sequent().formulaNumberInSequent(
                oldRuleApp.
                posInOccurrence().
                isInAntec(),
                oldRuleApp.posInOccurrence().constrainedFormula());
        return PosInOccurrence.findInSequent(pair.goal.sequent(),
                formulaNumber, oldRuleApp.posInOccurrence().posInTerm());
    }
    
    
    
    /**
     * Used for rebuilding the tree: Joins the node of the old sub trees and the corresponding 
     * goals in the new tree to one object. 
     * Return by reference: both <code>pairs</code> and <code>openLeaves</code> are manipulated. 
     *     */
    private int add(LinkedList<NodeGoalPair> pairs,
                     LinkedList<NodeGoalPair> openLeaves, 
                     Iterator<Node> iterator, LinkedList<Goal> goals){
        
        int leafNumber = 0;
        if(goals.isEmpty()){
        	return leafNumber;
        }
        while(iterator.hasNext()){
        	Goal matchedGoal = goals.pollFirst();
        	Node child = iterator.next();
        	
            if(!child.leaf()){
                pairs.add(new NodeGoalPair(child,matchedGoal));
            }else{
                if(!matchedGoal.node().isClosed()){
                    openLeaves.add(new NodeGoalPair(child,matchedGoal));
                }          
                leafNumber++;
            }
        }
        return leafNumber;

    }
    
    /**
     * This function uncovers the decision predicate that is hidden after applying the cut rule. 
     */
    private void uncoverDecisionPredicate(DelayedCut cut, List<NodeGoalPair> openLeaves){
        ImmutableList<NodeGoalPair> list = ImmutableSLList.<NodeGoalPair>nil();
        for(NodeGoalPair pair : openLeaves){
            list = list.append(new NodeGoalPair(pair.node,pair.goal.apply(cut.getHideApp()).head()));
        }
        cut.setGoalsAfterUncovering(list);
    }

    @Override
    public void run() {
        try{
            cut();
        }catch(Throwable throwable){
            for(DelayedCutListener listener : listeners){
                listener.eventException(throwable);
            }
        }
    }

    

}