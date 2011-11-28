package de.uka.ilkd.key.proof.delayedcut;

import java.io.IOException;
import java.util.HashMap;
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
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRuleApp;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.IfFormulaInstDirect;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This class is responsible for processing the delayed cut. The information about the cut 
 * is stored in  * <code>DelayCut</code>.
 *
 */
public class DelayedCutProcessor implements Runnable {
     
    private static final String HIDE_RIGHT_TACLET = "hide_right";
    private static final String HIDE_LEFT_TACLET  = "hide_left";
    private static final String CUT_TACLET = "cut";
    private static final int DEC_PRED_INDEX = 0;

    private final LinkedList<DelayedCutListener> listeners = new LinkedList<DelayedCutListener>();
    private final Proof proof;
    private final Node  node;
    private final Term  descisionPredicate;
    private final int   mode;
    
    private static class TacletCollection{
        FindTaclet hideRightTaclet;
        Taclet cutTaclet;
        FindTaclet hideLeftTaclet;
        TacletCollection(Proof proof){
            for(Taclet taclet : proof.env().getInitConfig().getTaclets()){
                if(taclet.name().toString().equals(HIDE_RIGHT_TACLET)){
                    hideRightTaclet = (FindTaclet)taclet;
                }else  if(taclet.name().toString().equals(CUT_TACLET)){
                    cutTaclet = taclet; 
                }  if(taclet.name().toString().equals(HIDE_LEFT_TACLET)){
                    hideLeftTaclet = (FindTaclet)taclet; 
                }                
            }
        }
        public String toString(){
            String s = "hideRightTaclet: " + (hideRightTaclet != null) + "\n"+
                        "hideLeftTaclet: " + (hideLeftTaclet != null) + "\n"+
                        "cutTaclet: " + (cutTaclet != null) + "\n";
            return s;
        }
    }
    

    
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
    
    public void cut(){
        
        for(DelayedCutListener listener : listeners){
            listener.eventCutting();
        }
         // do not change the order of the following two statements!
         RuleApp firstAppliedRuleApp = node.getAppliedRuleApp(); 
         Node subtrees [] = proof.pruneProof(node, false);
         
         TacletCollection taclets = new TacletCollection(proof);
         
         DelayedCut delayedCut = new DelayedCut(proof, node,
                                                descisionPredicate, subtrees,
                                                mode,firstAppliedRuleApp);
         
        
         ImmutableList<Goal> cutResult = cut(delayedCut,taclets);       
         
         ImmutableList<Goal> hideResult = hide(delayedCut,getGoalForHiding(cutResult, delayedCut),taclets);
         
         
         
         List<Goal> openLeaves = rebuildSubTrees(delayedCut, hideResult.head());
 
         uncoverDecisionPredicate(delayedCut, openLeaves);

         for(DelayedCutListener listener : listeners){
             listener.eventEnd(delayedCut);
         }
       
         
    }
    
    
   
    
    
    
    
    private ImmutableList<Goal> cut(DelayedCut cut,
            TacletCollection taclets){
        Goal goal = find(cut.getProof(), cut.getNode());
        
        

        
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(taclets.cutTaclet);
        
        app = app.addCheckedInstantiation(app.uninstantiatedVars().iterator().next(),
                                    cut.getFormula(),cut.getServices(), true);
    
       return goal.apply(app);
    }
    
    private ImmutableList<Goal> hide(DelayedCut cut, Goal goal, TacletCollection taclets){
        FindTaclet hideTaclet = getHideTaclet(cut, taclets);
        SVInstantiations inst =
        SVInstantiations.EMPTY_SVINSTANTIATIONS.add(
                getSVofHideTaclet(hideTaclet),
                cut.getFormula(), cut.getServices());
      
        SequentFormula sf = getSequentFormula(goal, cut.isDecisionPredicateInAntecendet());
        
        
        PosInOccurrence pio = new PosInOccurrence(sf,PosInTerm.TOP_LEVEL,
                cut.isDecisionPredicateInAntecendet());
        
        TacletApp app = PosTacletApp.createPosTacletApp(hideTaclet,inst,
                pio,
            cut.getServices());
        ImmutableList<Goal> result = goal.apply(app);
        cut.setHideApp(result.head().node().getLocalIntroducedRules().iterator().next());
        return result;
    }
    
    private Goal getGoalForHiding(ImmutableList<Goal> goals, DelayedCut cut){
        assert goals.size() == 2;
        Goal [] goal = {goals.head(),goals.tail().head()};
       
          
        for(int i=0; i < 2; i++){
             String side = cut.isDecisionPredicateInAntecendet() 
                     ? "TRUE":"FALSE";
           
            if(goal[i].node().getNodeInfo().getBranchLabel().endsWith(side)){
                SequentFormula formula = getSequentFormula(goal[i], cut.isDecisionPredicateInAntecendet());
                if(formula.formula() == cut.getFormula()){
                    return goal[i];
                }
            }
        }
        throw new IllegalStateException("After a cut a goal belongs to the left or right side of the tree");
    }
    
    private SchemaVariable getSVofHideTaclet(Taclet taclet){
        return  taclet.getIfFindVariables().iterator().next();
    }
    
    private FindTaclet getHideTaclet(DelayedCut cut, TacletCollection taclets){
        return cut.isDecisionPredicateInAntecendet() ? taclets.hideLeftTaclet :
            taclets.hideRightTaclet;        
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
            
  
            totalNumber -= add(pairs,openLeaves,pair.node,pair.goal.apply(app));
            for(DelayedCutListener listener : listeners){
                listener.eventRebuildingTree(++currentNumber, totalNumber);
            }
        }
        return openLeaves;
    }
    
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
    
    private PosInOccurrence translate(NodeGoalPair pair){
        RuleApp oldRuleApp = pair.node.getAppliedRuleApp();
        if(oldRuleApp.posInOccurrence() == null){
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
        int i=0;
        for(Goal goal : goals){            
            pairs.add(new NodeGoalPair(subtrees[i], goal));
            i++;
        }
    }
    
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
    
    private void uncoverDecisionPredicate(DelayedCut cut, List<Goal> openLeaves){
        for(Goal goal : openLeaves){
            goal.apply(cut.getHideApp());
        }
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
















