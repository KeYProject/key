package de.uka.ilkd.key.proof.delayedcut;

import java.io.IOException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

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
public class DelayedCutProcessor {
    public static DelayedCutProcessor INSTANCE = new DelayedCutProcessor();
    
    private static final String HIDE_RIGHT_TACLET = "hide_right";
    private static final String HIDE_LEFT_TACLET  = "hide_left";
    private static final String CUT_TACLET = "cut";
    private static final int DEC_PRED_INDEX = 0;

    
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
    
    private HashMap<Proof, TacletCollection> tacletCollection = 
            new HashMap<Proof,TacletCollection>();
    
    private TacletCollection getTaclets(Proof proof){
        TacletCollection tc = tacletCollection.get(proof);
        if(tc == null){
            tc = new TacletCollection(proof);
            tacletCollection.put(proof, tc);
        }
        return tc;
    }
    
    
    private DelayedCutProcessor() {}
    
    private Goal find(Proof proof, Node node){
        for(Goal goal : proof.openGoals()){
            if(goal.node() == node){
                return goal;
            }
        }
        return null;
    }
    
    public boolean cut(Proof proof, Node node, Term formula, int mode){
        System.out.println("BEGIN CUT");
         // do not change the order of the following two statements!
         RuleApp firstAppliedRuleApp = node.getAppliedRuleApp(); 
         Node subtrees [] = proof.pruneProof(node, false);
         
         TacletCollection taclets = getTaclets(proof);
         
         DelayedCut delayedCut = new DelayedCut(proof, node,
                                                formula, subtrees,
                                                mode,firstAppliedRuleApp);
        
         ImmutableList<Goal> cutResult = cut(delayedCut,taclets);       
         
         ImmutableList<Goal> hideResult = hide(delayedCut,getGoalForHiding(cutResult, delayedCut),taclets);
         
         rebuildSubTrees(delayedCut, hideResult.head());

         proof.fireProofGoalsChanged();
         return true;
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
        return goal.apply(app);
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
    
    private void rebuildSubTrees(DelayedCut cut, Goal goal){
        System.out.println("###BEGIN###");
        LinkedList<NodeGoalPair> pairs = new LinkedList<NodeGoalPair>();
 
        add(pairs,cut.getSubtrees(),goal.apply(
                cut.getFirstAppliedRuleApp()));

        while(!pairs.isEmpty()){
            
            NodeGoalPair pair = pairs.pollLast();
            
            System.out.println("Apply rule of " +pair.node.serialNr());
            System.out.println("Apply rule on " + pair.goal.node().serialNr()); 
            RuleApp app = createNewRuleApp(pair,
                    cut.getServices());
            add(pairs,pair.node,pair.goal.apply(app));
        }
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
        int formulaNumber = pair.node.sequent().formulaNumberInSequent(oldRuleApp.posInOccurrence().isInAntec(),
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
    
    private void add(LinkedList<NodeGoalPair> pairs, Node parent, ImmutableList<Goal> goals){
        assert parent.childrenCount() == goals.size();
        int i=0; 
        for(Goal goal : goals){
            if(!parent.child(i).leaf()){
                pairs.add(new NodeGoalPair(parent.child(i),goal));
            }
            i++;
        }
    }

    

}
















