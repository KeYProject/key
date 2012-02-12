package de.uka.ilkd.key.proof.join;

import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.TreeSet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TacletFilter;
import de.uka.ilkd.key.proof.delayedcut.DelayedCut;
import de.uka.ilkd.key.proof.delayedcut.DelayedCutProcessor;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;

public class JoinProcessor implements Runnable{
    private boolean used = false;
    private final Proof proof;
    private final Services services;
    private final ProspectivePartner partner;
    private final LinkedList<Listener> listeners = new LinkedList<Listener>();
    private static final String HIDE_RIGHT_TACLET = "hide_right";
    public static final String SIMPLIFY_UPDATE [] =    {"simplifyIfThenElseUpdate1",
    													"simplifyIfThenElseUpdate2",
    													"simplifyIfThenElseUpdate3"};



    
    public interface Listener{
        public void exceptionWhileJoining(Throwable e);
        public void endOfJoining(ImmutableList<Goal> goals);
    }
    
    public JoinProcessor(ProspectivePartner partner, Proof proof) {
        super();
        this.proof = proof;
        this.services = proof.getServices();
        this.partner = partner;
    }

    public void join(){        
        if(used){
            throw new IllegalStateException("Every instance can only be used once.");
        }
        used= true;
        processJoin();
        
    }
    
    public void addListener(Listener listener){
        listeners.add(listener);
    }
    
    private void processJoin(){

        Term cutFormula = createCutFormula();
        
        DelayedCutProcessor cutProcessor = new DelayedCutProcessor(proof,
                                                partner.getCommonParent(),
                                                cutFormula,
                                                DelayedCut.DECISION_PREDICATE_IN_ANTECEDENT);
        
        DelayedCut cut = cutProcessor.cut();
 
        Goal result = hide(cut.getRemainingGoal());
        
        simplifyUpdate(result,cut);
  
        for(Listener listener : listeners){
            listener.endOfJoining(cut.getGoalsAfterUncovering());
        }
    }
    

    
    private SequentFormula findFormula(Sequent sequent,Term content, boolean antecedent){
        for(SequentFormula sf : (antecedent ? sequent.antecedent() : sequent.succedent())){
            if(sf.formula().equals(content)){
                return sf;
            }
        }
        return null;
    }
    
    private void simplifyUpdate(Goal goal, DelayedCut cut){

        SequentFormula sf = findFormula(goal.sequent(), cut.getFormula(), false);
        
        PosInOccurrence pio = new PosInOccurrence(sf,PosInTerm.TOP_LEVEL.down(0),false);
        
        if(apply(SIMPLIFY_UPDATE, goal, pio)== null){
        	pio = new PosInOccurrence(sf,PosInTerm.TOP_LEVEL,false);
        	ImmutableList<RuleApp> builtInApps =goal.ruleAppIndex().getBuiltInRules(goal, pio);
        	for(RuleApp app : builtInApps){
        		if(app.rule() == OneStepSimplifier.INSTANCE){
        			goal.apply(app);
        		}
        	}
        }
    }
    
    /**Applies one of the given taclets if this possible otherwise an exception is thrown.*/
    private ImmutableList<Goal> apply(final String [] tacletNames,Goal goal, PosInOccurrence pio){
    	

        TacletFilter filter = new TacletFilter() {
            
            @Override
            protected boolean filter(Taclet taclet) {
                for(String tacletName : tacletNames){
                	if( taclet.name().toString().equals(tacletName)){
                		return true;
                	}
                }
                return false;
            }
            
            
        };
        ImmutableList<NoPosTacletApp> apps =  goal.ruleAppIndex().getFindTaclet(filter,pio, services);
        
        if(apps.isEmpty()){
        	return null;

        }
        NoPosTacletApp app = apps.head();
        
        PosTacletApp app2 = app.setPosInOccurrence(pio, services);
        return goal.apply(app2); 
    }

    
    private Goal hide(Goal goal){
    	if(partner.getFormulaForHiding() == null){
    		return goal;
    	}
        int index = goal.sequent().formulaNumberInSequent(false,partner.getFormulaForHiding());
        PosInOccurrence pio = PosInOccurrence.findInSequent(goal.sequent(),
                index, PosInTerm.TOP_LEVEL);
        return apply(new String [] {HIDE_RIGHT_TACLET}, goal, pio).head();
        
    }
    
    
    private Term createCutFormula(){
        Term ifElseTerm = buildIfElseTerm();
        Term phi = createPhi();
        return TermBuilder.DF.or(ifElseTerm, phi);
    }
    
    private Term buildIfElseTerm(){
         Term thenTerm = TermBuilder.DF.apply(partner.getUpdate(0),partner.getCommonFormula());
         Term elseTerm = TermBuilder.DF.apply(partner.getUpdate(1),partner.getCommonFormula());
         
         return TermBuilder.DF.ife(partner.getCommonPredicate(), thenTerm,elseTerm);
        
    }
    
    private Term createPhi(){
         Collection<Term> commonDelta = computeCommonFormulas(partner.getSequent(0).succedent(),
                                                              partner.getSequent(1).succedent(),
                                                              partner.getCommonFormula());
         Collection<Term> commonGamma = computeCommonFormulas(partner.getSequent(0).antecedent(),
                                                              partner.getSequent(1).antecedent(),
                                                              partner.getCommonFormula());
         Collection<Term> delta1      = computeDifference(partner.getSequent(0).succedent(),commonDelta,partner.getFormula(0).formula());
         Collection<Term> delta2      = computeDifference(partner.getSequent(1).succedent(),commonDelta,partner.getFormula(1).formula());
         
         Collection<Term> gamma1      = computeDifference(partner.getSequent(0).antecedent(),commonGamma,null);
         Collection<Term> gamma2      = computeDifference(partner.getSequent(1).antecedent(),commonGamma,null);
         
         Collection<Term> constrainedGamma1 = createConstrainedTerms(gamma1, partner.getCommonPredicate(), true);
         Collection<Term> constrainedGamma2 = createConstrainedTerms(gamma2, TermBuilder.DF.not(partner.getCommonPredicate()), true);
         

         Collection<Term> constrainedDelta1 = createConstrainedTerms(delta1, partner.getCommonPredicate(), false);
         Collection<Term> constrainedDelta2 = createConstrainedTerms(delta2, TermBuilder.DF.not(partner.getCommonPredicate()), false);
         
         Term phi = TermBuilder.DF.ff();
         phi = createDisjunction(phi,commonGamma,true);
         phi = createDisjunction(phi,constrainedGamma1,true);
         phi = createDisjunction(phi,constrainedGamma2,true);
         

         phi = createDisjunction(phi,commonDelta,false);
         phi = createDisjunction(phi,constrainedDelta1,false);
         phi = createDisjunction(phi,constrainedDelta2,false);
         
         return phi;
    }
    
    private Term createDisjunction(Term seed, Collection<Term> formulas, boolean needNot ){
        for(Term formula : formulas){
            if(needNot){
                seed = TermBuilder.DF.or(seed,TermBuilder.DF.not(formula));
            }else{
                seed = TermBuilder.DF.or(seed,formula);
            }
        }
        return seed;
    }
    
    private Collection<Term> createConstrainedTerms(Collection<Term> terms, Term predicate,boolean gamma){
        Collection<Term> result = new LinkedList<Term>();
        for(Term term : terms){
            if(gamma){
                result.add(TermBuilder.DF.imp(predicate,term));
            }else{
                result.add(TermBuilder.DF.and(predicate,term));
            }
        }
        return result;
    }
    
    private Collection<Term> computeCommonFormulas(Semisequent s1, Semisequent s2, Term exclude){
        TreeSet<Term> formulas1 = createTree(s1, exclude);
        TreeSet<Term> result = createTree();
        for(SequentFormula sf : s2){
            if(formulas1.contains(sf.formula())){
                result.add(sf.formula());
            }
        }
        return result;
    }
    
    private Collection<Term> computeDifference(Semisequent s, Collection<Term> excludeSet, Term exclude){
        LinkedList<Term> result = new LinkedList<Term>();
        for(SequentFormula sf : s){
            if(sf.formula() != exclude && !excludeSet.contains(sf.formula())){
                result.add(sf.formula());
            }
        }
        return result;
    }
    
    private TreeSet<Term> createTree(Semisequent semisequent, Term exclude){
        TreeSet<Term> set = createTree();
        for(SequentFormula sf : semisequent){
            if(sf.formula() != exclude){
                set.add(sf.formula());
            }
        }
        return set;
    }
    
    private TreeSet<Term> createTree(){
        return new TreeSet<Term>(new Comparator<Term>() {

            @Override
            public int compare(Term o1, Term o2) {
                return o1.serialNumber()-o2.serialNumber();
            }
        });
    }

    @Override
    public void run() {
        try{
        join();
        }catch(Throwable e){
            for(Listener listener : listeners){
                listener.exceptionWhileJoining(e);
            }
        }
    }

}
