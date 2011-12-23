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
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TacletFilter;
import de.uka.ilkd.key.rule.BuiltInRuleApp;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
    
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
        used = false;
        for(DelayedCutListener listener : listeners){
            listener.eventCutting();
        }
         // do not change the order of the following two statements!
         RuleApp firstAppliedRuleApp = node.getAppliedRuleApp(); 
         Node subtrees [] = proof.pruneProof(node,false);
         
         
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
         List<Goal> openLeaves = rebuildSubTrees(delayedCut, result.head());
 
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
    
    private static class NodeGoalPair{
        final Node node; 
        final Goal goal;
        public NodeGoalPair(Node node, Goal goal) {
            super();
            this.node = node;
            this.goal = goal;
        }
        
    }
    
    /**
     * Rebuilds the subtree pruned by the process, that is the rules are replayed. 
     *  */
    private List<Goal> rebuildSubTrees(DelayedCut cut, Goal goal){
        LinkedList<NodeGoalPair> pairs = new LinkedList<NodeGoalPair>();
        LinkedList<Goal>  openLeaves = new LinkedList<Goal>();
 
        add(pairs,cut.getSubtrees(),goal.apply(
                cut.getFirstAppliedRuleApp()));
        
        int totalNumber = 0;
        for(NodeGoalPair pair : pairs){
            totalNumber += pair.node.countNodes();
        }

        int currentNumber =0;
        while(!pairs.isEmpty()){
            
            NodeGoalPair pair = pairs.pollLast();

            RuleApp app = createNewRuleApp(pair,
                    cut.getServices());
         
            totalNumber -= add(pairs,openLeaves,pair.node,
                   pair.goal.apply(app));
 

            for(DelayedCutListener listener : listeners){
                listener.eventRebuildingTree(++currentNumber, totalNumber);
            }
        }
        return openLeaves;
    }
    
    /**
     * Based on an old rule application a new rule application is built. Mainly 
     * the position is updated.
     */
    private RuleApp createNewRuleApp(NodeGoalPair pair, Services services){
        RuleApp oldRuleApp = pair.node.getAppliedRuleApp();
        
        
        PosInOccurrence newPos = translate(pair);

        if(oldRuleApp instanceof PosTacletApp){
            PosTacletApp app = (PosTacletApp) oldRuleApp; 
            return PosTacletApp.createPosTacletApp((FindTaclet)app.taclet(),
                    app.instantiations(),app.ifFormulaInstantiations(),
                    newPos
                    ,services);
        }

        if(oldRuleApp instanceof BuiltInRuleApp){
            BuiltInRuleApp app = (BuiltInRuleApp) oldRuleApp;
            return new BuiltInRuleApp(app.rule(), translate(pair), app.ifInsts());
        }
        return oldRuleApp;
        
    }
    
    /**
     * Translates the position of an old rule application into the position of 
     * a new rule application.
     */
    private PosInOccurrence translate(NodeGoalPair pair){
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
    
    private void add(LinkedList<NodeGoalPair> pairs, Node [] subtrees, ImmutableList<Goal> goals){
        
        assert subtrees.length == goals.size(); 
        
        for(Goal goal : goals){   
            for(int i=0; i < subtrees.length; i++){
                if(!subtrees[i].leaf() && nodesAreEqual(subtrees[i], goal.node())){
                    pairs.add(new NodeGoalPair(subtrees[i], goal));
                }    
            }
            
           
        }
    }
    
    private boolean nodesAreEqual(Node node1, Node node2){
        if(node1.sequent().size() != node2.sequent().size()){
            return false;
        }
        Iterator<SequentFormula> it1 = node1.sequent().iterator();
        Iterator<SequentFormula> it2 = node2.sequent().iterator();
        while(it1.hasNext()){
            if(it1.next().formula() != it2.next().formula()){
                return false;
            }
        }
        return true;
        
    }
    
    /**
     * Used for rebuilding the tree: Joins the node of the old sub trees and the corresponding 
     * goals in the new tree to one object. 
     * Return by reference: both <code>pairs</code> and <code>openLeaves</code> are manipulated. 
     *     */
    private int add(LinkedList<NodeGoalPair> pairs,
                     LinkedList<Goal> openLeaves, 
                     Node parent, ImmutableList<Goal> goals){
        assert parent.childrenCount() == goals.size();
        int leafNumber = 0;
        int i=0;
        for(Goal goal : goals){
            if(!parent.child(i).leaf()){
                pairs.add(new NodeGoalPair(parent.child(i),goal));
            }else{
                if(!goal.node().isClosed()){
                    openLeaves.add(goal);
                }          
                leafNumber++;
            }
            i++;            
        }
        return leafNumber;

    }
    
    /**
     * This function uncovers the decision predicate that is hidden after applying the cut rule. 
     */
    private void uncoverDecisionPredicate(DelayedCut cut, List<Goal> openLeaves){
        ImmutableList<Goal> list = ImmutableSLList.<Goal>nil();
        for(Goal goal : openLeaves){
            list = list.append(goal.apply(cut.getHideApp()));
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
















