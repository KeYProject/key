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

package de.uka.ilkd.key.rule.conditions;

import java.util.Comparator;
import java.util.LinkedList;
import java.util.TreeMap;
import java.util.TreeSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class SimplifyIfThenElseUpdateCondition implements VariableCondition {
  
    private final FormulaSV phi;
    private final UpdateSV u1;
    private final UpdateSV u2;
    private final FormulaSV   commonFormula;
    private final SchemaVariable result;
    

    
    
    public SimplifyIfThenElseUpdateCondition(FormulaSV phi, UpdateSV u1, UpdateSV u2, FormulaSV commonFormula,
            SchemaVariable result) {
        super();
        this.phi = phi;
        this.u1 = u1;
        this.u2 = u2;
        this.commonFormula = commonFormula;
        this.result = result;
    }
    
    private static class ElementaryUpdateWrapper {
        private UpdateableOperator op;

        private Term               rhs1;
        private Term               rhs2;
        
        public ElementaryUpdateWrapper(UpdateableOperator op, TermServices services) {
            super();
            this.op = op;
            Term identity = services.getTermFactory().createTerm(op);
             
            rhs1 = identity;
            rhs2 = identity;
        }
        
        public Term createIfElseTerm(Term phi, TermServices services){
            if(rhs1.equals(rhs2)){
                return services.getTermBuilder().elementary(op, rhs1);
            }
            Term ifThenElse = services.getTermBuilder().ife(phi, rhs1, rhs2);
            return services.getTermBuilder().elementary(op, ifThenElse);
            
        }
        
        public void setRhs1(Term rhs1) {
            this.rhs1 = rhs1;
        }
        public void setRhs2(Term rhs2) {
            this.rhs2 = rhs2;
        }

        
    }
    
    private TreeMap<UpdateableOperator,ElementaryUpdateWrapper> createMap(){
        return new TreeMap<UpdateableOperator, 
                ElementaryUpdateWrapper>(new Comparator<UpdateableOperator>() {

            @Override
            public int compare(UpdateableOperator o1, UpdateableOperator o2) {
                
                return o1.name().compareTo(o2.name());
            }
        });
    }
    
    private TreeSet<UpdateableOperator> createTree(){
        return new TreeSet<UpdateableOperator>(new Comparator<UpdateableOperator>() {

            @Override
            public int compare(UpdateableOperator o1, UpdateableOperator o2) {
                
                return o1.name().compareTo(o2.name());
            }
        });
    }
    
    private void collectSingleTerm(final TreeMap<UpdateableOperator, ElementaryUpdateWrapper> map, 
            Term update,final boolean firstTerm, TermServices services){
                ElementaryUpdate eu = (ElementaryUpdate) update.op();
                ElementaryUpdateWrapper euw= null;
                if(!map.containsKey(eu.lhs())){
                    euw = new ElementaryUpdateWrapper( eu.lhs(), services);
                    map.put(eu.lhs(), euw);
                }else{
                    euw = map.get(eu.lhs());
                }
                if(firstTerm){
                    euw.setRhs1(update.sub(0));
                }else{
                    euw.setRhs2(update.sub(0));
                }
            }

    
    private boolean collect(final TreeMap<UpdateableOperator, ElementaryUpdateWrapper> map, 
                         Term update,final boolean firstTerm, TermServices services){
        LinkedList<Term> updates = new LinkedList<Term>();
        TreeSet<UpdateableOperator> collected = createTree();
        updates.add(update);
        // consider only parallel updates, where each variable occurs only once on 
        // the left hand side.
        while(!updates.isEmpty()){
            Term next = updates.poll();
            if(next.op() == UpdateJunctor.PARALLEL_UPDATE){
                 updates.add(next.sub(0));
                 updates.add(next.sub(1));
            }else if(next.op() == UpdateJunctor.SKIP){
            	return true;            	
            }else if(next.op() instanceof ElementaryUpdate){
                ElementaryUpdate eu = (ElementaryUpdate) next.op();
                 if(collected.contains(eu.lhs())){
                     return false;
                 }
                 collected.add(eu.lhs());
                 collectSingleTerm(map, next, firstTerm, services);
            }else{
                return false;
            }
        }
        return true;

    }

    private Term simplify(Term phi, Term u1, Term u2, Term t, TermServices services){

        TreeMap<UpdateableOperator, ElementaryUpdateWrapper> map = createMap();
        
        if(!collect(map,u1,true, services)){
            
            return null;
        }
        if(!collect(map,u2,false, services)){
            return null;
        }
        Term result = services.getTermBuilder().skip();
        for(ElementaryUpdateWrapper euw : map.values()){
            result = services.getTermBuilder().parallel(result, euw.createIfElseTerm(phi, services));
        }
        
        result = services.getTermBuilder().apply(result, t, null);
        return result;
    }
    

    @Override
    public MatchConditions check(SchemaVariable var,
            SVSubstitute instCandidate, MatchConditions mc,
            Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        
        Term u1Inst      = (Term) svInst.getInstantiation(u1);
        Term u2Inst      = (Term) svInst.getInstantiation(u2);
        Term tInst      = (Term) svInst.getInstantiation(commonFormula);
        Term phiInst    = (Term) svInst.getInstantiation(phi);
        Term resultInst = (Term) svInst.getInstantiation(result);
        
        if(tInst==null || phiInst==null) {
            return mc;
        }
        
        u1Inst = u1Inst == null ? services.getTermBuilder().skip() : u1Inst;
        u2Inst = u2Inst == null ? services.getTermBuilder().skip() : u2Inst;

        Term properResultInst = simplify(phiInst, u1Inst, u2Inst, tInst, services);
        if(properResultInst == null) {
            return null;
        } else if(resultInst == null) {
            svInst = svInst.add(result, properResultInst, services);
            return mc.setInstantiations(svInst);
        } else if(resultInst.equals(properResultInst)) {
            return mc;
        } else {
            return null;
        }

    }

}
