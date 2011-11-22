package de.uka.ilkd.key.proof.delayedcut;

import java.util.HashMap;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
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
    
    public boolean cut(Proof proof, Node node, DelayedCutCompletion completion){
         Node subtrees [] = proof.pruneProof(node, false);
         
         TacletCollection taclets = getTaclets(proof);
         DelayedCut delayedCut = new DelayedCut(proof, node, null, subtrees);
        
         Goal goal = find(proof, node);
    
         if(!completion.complete(NoPosTacletApp.createNoPosTacletApp(taclets.cutTaclet), goal)){
             return false;
         }
        
         System.out.println(goal.node().serialNr());
         
         
         
         proof.fireProofGoalsChanged();
         return true;
    }
    

}
















