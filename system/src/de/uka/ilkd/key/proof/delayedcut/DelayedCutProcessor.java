package de.uka.ilkd.key.proof.delayedcut;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.IfFormulaInstDirect;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.PosTacletApp;
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
    private static final int FORMULA_INDEX = 0;

    
    private static class TacletCollection{
        Taclet hideRightTaclet;
        Taclet cutTaclet;
        Taclet hideLeftTaclet;
        TacletCollection(Proof proof){
            for(Taclet taclet : proof.env().getInitConfig().getTaclets()){
                if(taclet.name().toString().equals(HIDE_RIGHT_TACLET)){
                    hideRightTaclet = taclet;
                }else  if(taclet.name().toString().equals(CUT_TACLET)){
                    cutTaclet = taclet; 
                }  if(taclet.name().toString().equals(HIDE_LEFT_TACLET)){
                    hideLeftTaclet = taclet; 
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
         Node subtrees [] = proof.pruneProof(node, false);
         
         TacletCollection taclets = getTaclets(proof);
         
         DelayedCut delayedCut = new DelayedCut(proof, node, formula, subtrees,mode);
        
         ImmutableList<Goal> cutResult = cut(delayedCut,taclets);       
         
         Goal goal = getGoal(cutResult, delayedCut);
         
         System.out.println("goal: " + goal.node().serialNr());
         
         
         
//         SVInstantiations inst =
//         SVInstantiations.EMPTY_SVINSTANTIATIONS.add(
//                 taclets.hideLeftTaclet.getIfFindVariables().iterator().next(),
//                 formula, proof.getServices());
//         
      //  app = PosTacletApp.createPosTacletApp((FindTaclet)taclets.hideLeftTaclet,inst,
            //    PosInOccurrence.findInSequent(firstGoal.sequent(),1, PosInTerm.TOP_LEVEL),
         //       proof.getServices());
//         firstGoal.apply(app);
 
         proof.fireProofGoalsChanged();
         return true;
    }
    
    
    private void hide(DelayedCut cut, Goal goal){
        
    }
    
    
    private ImmutableList<Goal> cut(DelayedCut cut,
            TacletCollection taclets){
        Goal goal = find(cut.getProof(), cut.getNode());
        
        

        
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(taclets.cutTaclet);
        
        app = app.addCheckedInstantiation(app.uninstantiatedVars().iterator().next(),
                                    cut.getFormula(),cut.getServices(), true);
  
       return goal.apply(app);
    }
    
    private Goal getGoal(ImmutableList<Goal> goals, DelayedCut cut){
        assert goals.size() == 2;
        Goal [] goal = {goals.head(),goals.tail().head()};
       
          
        for(int i=0; i < 2; i++){
             String side = cut.getCutMode() == DelayedCut.FORMULA_ON_LEFT_SIDE ? "TRUE":"FALSE";
           
            if(goal[i].node().getNodeInfo().getBranchLabel().endsWith(side)){
                SequentFormula formula = getSequentFormula(goal[i], cut.getCutMode());
                if(formula.formula() == cut.getFormula()){
                    return goal[i];
                }
            }
        }
        throw new IllegalStateException("After a cut a goal belongs to the left or right side of the tree");
    }
    
    private SequentFormula getSequentFormula(Goal goal, int mode){
        return (mode == DelayedCut.FORMULA_ON_LEFT_SIDE)?
                goal.sequent().antecedent().get(FORMULA_INDEX): 
                    goal.sequent().succedent().get(FORMULA_INDEX);
        
    }

    

}
















