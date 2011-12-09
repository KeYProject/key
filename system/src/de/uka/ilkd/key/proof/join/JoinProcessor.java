package de.uka.ilkd.key.proof.join;

import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.TreeSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.delayedcut.DelayedCut;
import de.uka.ilkd.key.proof.delayedcut.DelayedCutProcessor;

public class JoinProcessor implements Runnable{
    private boolean used = false;
    private final Proof proof;
    private final Services services;
    private final ProspectivePartner partner;
    
    
    
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
    
    private void processJoin(){

        Term cutFormula = createCutFormula();
        
        DelayedCutProcessor cutProcessor = new DelayedCutProcessor(proof,
                                                partner.getCommonParent(),
                                                cutFormula,
                                                DelayedCut.DECISION_PREDICATE_IN_ANTECEDENT);
        
        cutProcessor.cut();
        
        
        System.out.println(LogicPrinter.quickPrintTerm(cutFormula, services));
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
         Collection<Term> delta1      = computeDifference(partner.getSequent(0).succedent(),commonDelta,partner.getFormula(0));
         Collection<Term> delta2      = computeDifference(partner.getSequent(1).succedent(),commonDelta,partner.getFormula(1));
         
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
        join();
    }

}
