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

package de.uka.ilkd.key.smt;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.smt.lang.SMTSort;
import de.uka.ilkd.key.smt.lang.SMTTerm;
import de.uka.ilkd.key.smt.lang.SMTTermCall;
import de.uka.ilkd.key.smt.lang.SMTTermITE;
import de.uka.ilkd.key.smt.lang.SMTTermMultOp;
import de.uka.ilkd.key.smt.lang.SMTTermNumber;
import de.uka.ilkd.key.smt.lang.SMTTermQuant;
import de.uka.ilkd.key.smt.lang.SMTTermUnaryOp;
import de.uka.ilkd.key.smt.lang.SMTTermVariable;

public class OverflowChecker {


	private SMTSort intsort;






	public OverflowChecker(SMTSort intsort) {
		super();
		this.intsort = intsort;
	}

	private int max(){

		int bound = (int) Math.pow(2, intsort.getBitSize());

		return bound/2 -1;		
	}

	private int min(){

		int bound = (int) Math.pow(2, intsort.getBitSize());
		return -bound/2;	

	}





	private SMTTerm increaseBitsize(SMTTerm t){
		SMTTerm zero = new SMTTermNumber(0, 1, null);
		SMTTerm one = new SMTTermNumber(1, 1, null);

		SMTTerm zeroInt = new SMTTermNumber(0, intsort.getBitSize(), intsort);
		SMTTerm condition = t.gte(zeroInt);
		
		SMTTerm trueCase = zero.concat(t);		
		SMTTerm falseCase = one.concat(t);
		
		

		return SMTTerm.ite(condition, trueCase, falseCase);		
	}

	private SMTTerm doubleBitsize(SMTTerm t){
		//000000...
		SMTTerm zero = new SMTTermNumber(0, intsort.getBitSize(), null);
		//111111...
		SMTTerm one = new SMTTermNumber(intsort.getBound()-1, intsort.getBitSize(), null);		
		
		SMTTerm zeroInt = new SMTTermNumber(0, intsort.getBitSize(), intsort);
		SMTTerm condition = t.gte(zeroInt);
		
		SMTTerm trueCase = zero.concat(t);		
		SMTTerm falseCase = one.concat(t);		

		return SMTTerm.ite(condition, trueCase, falseCase);
	}

	private SMTTerm createGuardForAdd(SMTTermMultOp t){
		
		List<SMTTerm> subs = new LinkedList<SMTTerm>();
		for(SMTTerm sub : t.getSubs()){
			subs.add(increaseBitsize(sub));
		}
		SMTTerm increasedTerm = new SMTTermMultOp(t.getOperator(), subs);

		long newbound = intsort.getBound() * 2;
		long newMaxInt = max();
		long newMinInt = newbound + min() ;

		SMTTermNumber max = new SMTTermNumber(newMaxInt, intsort.getBitSize() + 1, null);
		SMTTermNumber min = new SMTTermNumber(newMinInt, intsort.getBitSize() + 1, null);

		SMTTerm assertLEMax = increasedTerm.lte(max);
		SMTTerm assertGEMin = increasedTerm.gte(min);

		return assertLEMax.and(assertGEMin);		
	}

	private SMTTerm createGuardForMul(SMTTermMultOp t){
		List<SMTTerm> subs = new LinkedList<SMTTerm>();
		for(SMTTerm sub : t.getSubs()){
			subs.add(doubleBitsize(sub));
		}
		SMTTerm increasedTerm = new SMTTermMultOp(t.getOperator(), subs);

		long newbound = intsort.getBound() * intsort.getBound();
		long newMaxInt = max();
		long newMinInt = newbound + min() ;

		SMTTermNumber max = new SMTTermNumber(newMaxInt, intsort.getBitSize() * 2, null);
		SMTTermNumber min = new SMTTermNumber(newMinInt, intsort.getBitSize() * 2, null);

		SMTTerm assertLEMax = increasedTerm.lte(max);
		SMTTerm assertGEMin = increasedTerm.gte(min);

		return assertLEMax.and(assertGEMin);

	}

	private void getSubTerms(SMTTerm t,Set<SMTTerm> result){

		if(t instanceof SMTTermMultOp){

			SMTTermMultOp tm = (SMTTermMultOp) t;

			if(isArithmeticOperator(tm.getOperator())){

				result.add(tm);

				for(SMTTerm sub : tm.getSubs()){
					getSubTerms(sub, result);
				}


			}



		}	

	}

	private SMTTerm createGuard(Set<SMTTerm> terms){

		List<SMTTerm> args = createGuards(terms);		
		return SMTTerm.and(args);		
	}

	public List<SMTTerm> createGuards(Set<SMTTerm> terms) {
		 List<SMTTerm> args = new LinkedList<SMTTerm>();

		 for(SMTTerm t: terms){

			 if(t instanceof SMTTermMultOp){
				 SMTTermMultOp tm = (SMTTermMultOp) t;
				 if(isAddOp(tm.getOperator())){

					 args.add(createGuardForAdd(tm));					
				 }
				 else if(isMulOp(tm.getOperator())){
					 args.add(createGuardForMul(tm));
				 }

			 }


		 }
		 return args;
	 }

	 private boolean isArithmeticOperator(SMTTermMultOp.Op op){		
		 return op.equals(SMTTermMultOp.Op.BVSDIV) ||
				 op.equals(SMTTermMultOp.Op.BVSREM) ||
				 op.equals(SMTTermMultOp.Op.MUL)||
				 op.equals(SMTTermMultOp.Op.PLUS)||
				 op.equals(SMTTermMultOp.Op.MINUS)||
				 op.equals(SMTTermMultOp.Op.BVSMOD);		
	 }


	 private boolean isAddOp(SMTTermMultOp.Op op){
		 return op.equals(SMTTermMultOp.Op.PLUS)
				 ||	 op.equals(SMTTermMultOp.Op.MINUS);
	 }

	 private boolean isMulOp(SMTTermMultOp.Op op){
		 return op.equals(SMTTermMultOp.Op.MUL);
	 }

	 private boolean isComparisonOp(SMTTermMultOp.Op op){
		 return op.equals(SMTTermMultOp.Op.BVSGE) ||
				 op.equals(SMTTermMultOp.Op.BVSGT) ||
				 op.equals(SMTTermMultOp.Op.BVSLE)||
				 op.equals(SMTTermMultOp.Op.BVSLT)||
				 op.equals(SMTTermMultOp.Op.EQUALS);	
	 }

	 /**
	  * Adds a guard for the given term if that term may overflow.
	  * @param t
	  * @return
	  */
	 public SMTTerm addGuardIfNecessary(SMTTerm t){
		 Set<SMTTermVariable> vars = new HashSet<SMTTermVariable>();
		 return addGuardIfNecessary(t, vars);
	 }
	 /**
	  * Constructs a guarded term, if overflows are possible, otherwise returns the original term.
	  * @param t
	  * @param quantifiedVars
	  * @return
	  */
	 private SMTTerm addGuardIfNecessary(SMTTerm t, Set<SMTTermVariable> quantifiedVars){


		 if(t instanceof SMTTermMultOp){
			 SMTTermMultOp tm = (SMTTermMultOp) t;
			 //we look for comparison terms like a < b
			 if(isComparisonOp(tm.getOperator())){
				 SMTTerm left = tm.getSubs().get(0);
				 SMTTerm right = tm.getSubs().get(1);

				 Set<SMTTerm> leftSubs = new HashSet<SMTTerm>();
				 Set<SMTTerm> rightSubs = new HashSet<SMTTerm>();

				 getSubTerms(left, leftSubs); //sub terms of the left side
				 getSubTerms(right, rightSubs); //sub terms of the right side
				 
				 //classify sub terms in universally and existentially quantified subs
				 Set<SMTTerm> universalSubs = new HashSet<SMTTerm>();
				 Set<SMTTerm> existentialSubs = new HashSet<SMTTerm>();
				 
				 classifySubs(quantifiedVars, leftSubs, universalSubs,
						 existentialSubs);
				 classifySubs(quantifiedVars, rightSubs, universalSubs,
						 existentialSubs);
				 //create universal and existential guards
				 SMTTerm universalGuard = createGuard(universalSubs);
				 SMTTerm existentialGuard = createGuard(existentialSubs);

				 //return the guarded term
				 return existentialGuard.and(universalGuard.implies(t));
				 //return universalGuard.implies(existentialGuard.and(t));


			 }
		 }

		 return t;

	 }
	 /**
	  * Recursively adds overflow guards for non ground terms if necessary.
	  * @param t
	  */
	 public void processTerm(SMTTerm t){
		 Set<SMTTermVariable> uvars = new HashSet<SMTTermVariable>();
		 Set<SMTTermVariable> evars = new HashSet<SMTTermVariable>();
		 processTerm(t, uvars,evars);
	 }


	 private void processTerm(SMTTerm t, Set<SMTTermVariable> universalVars, Set<SMTTermVariable> existentialVars){

		 if(t instanceof SMTTermMultOp){
			 SMTTermMultOp tm = (SMTTermMultOp) t;			
			 List<SMTTerm> subs = tm.getSubs();
			 for(SMTTerm sub : subs){
				 processTerm(sub, universalVars,existentialVars);
			 }


		 }
		 else if(t instanceof SMTTermCall){
			 SMTTermCall tc = (SMTTermCall) t;
			 List<SMTTerm> subs = tc.getArgs();

			 for(SMTTerm sub : subs){
				 processTerm(sub, universalVars,existentialVars);
			 }			

		 }
		 else if(t instanceof SMTTermQuant){
			 SMTTermQuant tq = (SMTTermQuant) t;
			 SMTTerm sub = tq.getSub();
			 if(tq.getQuant().equals(SMTTermQuant.Quant.FORALL)){
				 universalVars.addAll(tq.getBindVars());
			 }
			 else{
				 existentialVars.addAll(tq.getBindVars());
			 }
			 

			 Set<SMTTerm> terms = new HashSet<SMTTerm>();

			 searchArithTerms(terms,tq.getSub(),universalVars,existentialVars,tq.getBindVars());



			 SMTTerm guard = createGuard(terms);
			 processTerm(sub,universalVars,existentialVars);
			 if(tq.getQuant().equals(SMTTermQuant.Quant.FORALL)){
				 tq.setSub(guard.implies(tq.getSub()));
				 universalVars.removeAll(tq.getBindVars());
			 }
			 else{
				 tq.setSub(guard.and(tq.getSub()));
				 existentialVars.removeAll(tq.getBindVars());
			 }





		 }
		 else if(t instanceof SMTTermUnaryOp){
			 SMTTermUnaryOp tu = (SMTTermUnaryOp) t;
			 SMTTerm sub = tu.getSub();
			 SMTTerm guarded = addGuardIfNecessary(sub, universalVars);
			 if(!sub.equals(guarded)){
				 tu.setSub(guarded);
			 }
			 processTerm(tu.getSub(), universalVars,existentialVars);
		 }
		 else if(t instanceof SMTTermITE){
			 SMTTermITE ite = (SMTTermITE) t;
			 SMTTerm cond = ite.getCondition();
			 SMTTerm trueCase = ite.getTrueCase();
			 SMTTerm falseCase = ite.getFalseCase();

			 processTerm(ite.getCondition(), universalVars,existentialVars);
			 processTerm(ite.getTrueCase(), universalVars,existentialVars);
			 processTerm(ite.getFalseCase(),universalVars,existentialVars);

			 SMTTerm gcond = addGuardIfNecessary(cond, universalVars);
			 SMTTerm gtrueCase = addGuardIfNecessary(trueCase, universalVars);
			 SMTTerm gfalseCase = addGuardIfNecessary(falseCase, universalVars);

			 if(!cond.equals(gcond)){
				 ite.setCondition(gcond);
			 }

			 if(!trueCase.equals(gtrueCase)){
				 ite.setTrueCase(gtrueCase);
			 }

			 if(!falseCase.equals(gfalseCase)){
				 ite.setFalseCase(gfalseCase);
			 }





		 }
	 }


	 /**
	  * Searches for non ground terms in sub, and stores them in terms. 
	  * Begin with empty lists. 
	  * @param terms list where the terms are stored
	  * @param sub the term to be searched
	  * @param universalVars universal variables
	  * @param existentialVars existential variables
	  * @param bind variables bounded by the current quantifier
	  */
	 public void searchArithTerms(Set<SMTTerm> terms, SMTTerm sub,
			 Set<SMTTermVariable> universalVars, Set<SMTTermVariable> existentialVars, List<SMTTermVariable> bind) {

		 if(sub instanceof SMTTermMultOp){			
			 SMTTermMultOp tm = (SMTTermMultOp) sub;			
			 for(SMTTerm t : tm.getSubs()){
				 searchArithTerms(terms, t, universalVars, existentialVars,bind);
			 }		
			 if(isArithmeticOperator(tm.getOperator())){				
				 if(acceptableTerm(tm,universalVars,existentialVars,bind)){
					 
					 
					 terms.add(tm);
				 }				
			 }		
		 }
		 else if(sub instanceof SMTTermCall){
			 SMTTermCall tc = (SMTTermCall) sub;
			 for(SMTTerm t : tc.getArgs()){
				 searchArithTerms(terms, t, universalVars, existentialVars,bind);
			 }
		 }
		 else if(sub instanceof SMTTermQuant){
			 SMTTermQuant tq = (SMTTermQuant) sub;
			 searchArithTerms(terms, tq.getSub(), universalVars, existentialVars,bind);
		 }
		 else if(sub instanceof SMTTermITE){
			 SMTTermITE ite = (SMTTermITE) sub;
			 searchArithTerms(terms, ite.getCondition(), universalVars, existentialVars,bind);
			 searchArithTerms(terms, ite.getTrueCase(), universalVars, existentialVars,bind);
			 searchArithTerms(terms, ite.getFalseCase(), universalVars, existentialVars,bind);
		 }
		 else if(sub instanceof SMTTermUnaryOp){
			 SMTTermUnaryOp tu = (SMTTermUnaryOp) sub;
			 searchArithTerms(terms, tu.getSub(), universalVars, existentialVars,bind);
		 }

	 }
	 /**
	  * Searches for arithmetical ground terms in sub and stores them in terms 
	  * @param terms
	  * @param sub
	  */
	 public void searchArithGroundTerms(Set<SMTTerm> terms, SMTTerm sub) {

		 if(sub instanceof SMTTermMultOp){			
			 SMTTermMultOp tm = (SMTTermMultOp) sub;			
			 for(SMTTerm t : tm.getSubs()){
				 searchArithGroundTerms(terms, t);
			 }		
			 if(isArithmeticOperator(tm.getOperator())){				
				 if(!containsVars(tm)){
					 terms.add(tm);
				 }				
			 }		
		 }
		 else if(sub instanceof SMTTermCall){
			 SMTTermCall tc = (SMTTermCall) sub;
			 for(SMTTerm t : tc.getArgs()){
				 searchArithGroundTerms(terms, t);
			 }
		 }
		 else if(sub instanceof SMTTermQuant){
			 SMTTermQuant tq = (SMTTermQuant) sub;
			 searchArithGroundTerms(terms, tq.getSub());
		 }
		 else if(sub instanceof SMTTermITE){
			 SMTTermITE ite = (SMTTermITE) sub;
			 searchArithGroundTerms(terms, ite.getCondition());
			 searchArithGroundTerms(terms, ite.getTrueCase());
			 searchArithGroundTerms(terms, ite.getFalseCase());
		 }
		 else if(sub instanceof SMTTermUnaryOp){
			 SMTTermUnaryOp tu = (SMTTermUnaryOp) sub;
			 searchArithGroundTerms(terms, tu.getSub());
		 }

	 }

	 private boolean acceptableTerm(SMTTermMultOp tm,
			 Set<SMTTermVariable> universalVars, Set<SMTTermVariable> existentialVars, List<SMTTermVariable> bind) {

		 boolean known = true, relevant = false;
		 
		 Set<SMTTerm> vars = new HashSet<SMTTerm>();
		 getVariables(tm, vars);
		 
		 for(SMTTerm v : vars){
			 if(!universalVars.contains(v) && !existentialVars.contains(v)){
				 known = false;
			 }
			 if(bind.contains(v)){
				 relevant = true;
			 }
		 }
//		 
//		 
//		 
//		 
//		 for(SMTTerm v : existentialVars){
//			 if(vars.contains(v)){
//				relevant = true; 
//			 }
//		 }
//		 for(SMTTerm v : universalVars){
//			 if(vars.contains(v)){
//				relevant = true; 
//			 }
//		 }
		 
		 return known && relevant;
	 }

	

	 private void getVariables(SMTTerm term, Set<SMTTerm> vars) {
		 if(term instanceof SMTTermMultOp){			
			 SMTTermMultOp tm = (SMTTermMultOp) term;			
			 for(SMTTerm t : tm.getSubs()){
				 getVariables(t, vars);
			 }	
			 
			 		
		 }
		 else if(term instanceof SMTTermCall){
			 SMTTermCall tc = (SMTTermCall) term;
			 for(SMTTerm t : tc.getArgs()){
				 getVariables(t, vars);
			 }
			 
		 }
		 else if(term instanceof SMTTermQuant){
			 SMTTermQuant tq = (SMTTermQuant) term;
			 getVariables(tq.getSub(), vars);
		 }
		 else if(term instanceof SMTTermITE){
			 SMTTermITE ite = (SMTTermITE) term;
			 getVariables(ite.getTrueCase(), vars);
			 getVariables(ite.getFalseCase(), vars);
			 getVariables(ite.getCondition(), vars);
		 }
		 else if(term instanceof SMTTermUnaryOp){
			 SMTTermUnaryOp tu = (SMTTermUnaryOp) term;
			 getVariables(tu.getSub(), vars);
		 }
		 else if(term instanceof SMTTermVariable){
			 vars.add(term);
		 }
		
	}

	private boolean containsVars(SMTTerm term) {

		 if(term instanceof SMTTermMultOp){			
			 SMTTermMultOp tm = (SMTTermMultOp) term;			
			 for(SMTTerm t : tm.getSubs()){
				 if(containsVars(t)){
					 return true;
				 }
			 }	
			 
			 return false;
			 		
		 }
		 else if(term instanceof SMTTermCall){
			 SMTTermCall tc = (SMTTermCall) term;
			 for(SMTTerm t : tc.getArgs()){
				 if(containsVars(t)){
					 return true;
				 }
			 }
			 return false;
		 }
		 else if(term instanceof SMTTermQuant){
			 SMTTermQuant tq = (SMTTermQuant) term;
			 return containsVars(tq.getSub());
		 }
		 else if(term instanceof SMTTermITE){
			 SMTTermITE ite = (SMTTermITE) term;
			 return containsVars(ite.getCondition()) ||
			 containsVars(ite.getTrueCase()) ||
			 containsVars(ite.getFalseCase());
		 }
		 else if(term instanceof SMTTermUnaryOp){
			 SMTTermUnaryOp tu = (SMTTermUnaryOp) term;
			 return containsVars(tu.getSub());
		 }
		 else if(term instanceof SMTTermVariable){
			 return true;
		 }
		 else{
			 return false;
		 }

	 }






	 /**
	  * @param universalVars
	  * @param subs
	  * @param universalSubs
	  * @param existentialSubs
	  */
	 private void classifySubs(Set<SMTTermVariable> universalVars,
			 Set<SMTTerm> subs, Set<SMTTerm> universalSubs,
			 Set<SMTTerm> existentialSubs) {
		 for(SMTTerm sub : subs){

			 if(isUniversalSub(sub, universalVars)){
				 universalSubs.add(sub);
			 }
			 else{
				 existentialSubs.add(sub);
			 }


		 }
	 }



	 private boolean isUniversalSub(SMTTerm t, Set<SMTTermVariable> universalVars){

		 if(t instanceof SMTTermMultOp){
			 SMTTermMultOp tm = (SMTTermMultOp) t;
			 for(SMTTerm sub : tm.getSubs()){
				 if(universalVars.contains(sub) || isUniversalSub(sub, universalVars)){
					 return true;
				 }
			 }

			 return false;

		 }
		 else{
			 return false;
		 }





	 }









}