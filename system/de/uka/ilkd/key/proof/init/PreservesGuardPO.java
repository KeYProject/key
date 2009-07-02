// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.util.Map;

import de.uka.ilkd.key.gui.DependsClauseDialog;
import de.uka.ilkd.key.java.abstraction.IteratorOfKeYJavaType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.SetOfKeYJavaType;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.IteratorOfClassInvariant;
import de.uka.ilkd.key.speclang.SetAsListOfClassInvariant;
import de.uka.ilkd.key.speclang.SetOfClassInvariant;
import de.uka.ilkd.key.util.Debug;


/**
 * The "PreservesGuard" proof obligation.
 */
public class PreservesGuardPO extends EnsuresPO {
    
    private final SetOfClassInvariant guardedInvs;
    private final SetOfKeYJavaType guard;
    private Term encapsulationFormula = null;
    private ListOfProofOblInput dependsPOs = SLListOfProofOblInput.EMPTY_LIST;

    
    public PreservesGuardPO(InitConfig initConfig,
	    		    ProgramMethod programMethod,
                            SetOfClassInvariant guardedInvs,
                            SetOfKeYJavaType guard) {
        super(initConfig,
              "PreservesGuard (" + programMethod + ")", 
              programMethod, 
              Op.BOX, 
              SetAsListOfClassInvariant.EMPTY_SET,
              false);
        this.guardedInvs = guardedInvs;
        this.guard       = guard;
    }
    
    
    /**
     * Retrieves the "Acc" predicate.
     */
    private Function getAccPred() throws ProofInputException {
        Function accFunc 
                = (Function) initConfig.funcNS().lookup(new Name("Acc"));
        
        if(accFunc == null) {
            throw new ProofInputException(
                    "Could not find the \"Acc\" predicate.\n"
                    + "Please make sure the corresponding library is active.");
        }
        
        return accFunc;
    }   
    
    
    /**
     * Extracts a depends clause syntactically from a term
     * (helper for getDependsClauseForInv()).
     */
    private SetOfLocationDescriptor extractDependsClauseFromTerm(Term term) {
        SetOfLocationDescriptor result 
                = SetAsListOfLocationDescriptor.EMPTY_SET;
        
        for(int i = 0; i < term.arity(); i++) {
            result = result.union(extractDependsClauseFromTerm(term.sub(i)));
        }
        
        if(term.op() instanceof NonRigid) {
            result = result.add(new BasicLocationDescriptor(term));
        }

        return result;
    }
    
    
    /**
     * Removes elements from a depends clause whose top level operator is 
     * declared in a guard class (helper for getDependsClauseForInv()).
     */
    private SetOfLocationDescriptor filterDependsClause(
                                            SetOfLocationDescriptor clause) {
       IteratorOfLocationDescriptor it = clause.iterator();
       while(it.hasNext()) {
           LocationDescriptor loc = it.next();
           
           if(loc instanceof BasicLocationDescriptor) {
               Operator op = ((BasicLocationDescriptor) loc).getLocTerm().op();
               
               KeYJavaType containingKjt = null;
               if(op instanceof ProgramVariable) { 
                   containingKjt 
                       = ((ProgramVariable) op).getContainerType();
               }
               
               if(containingKjt != null) {
                   IteratorOfKeYJavaType it2 = guard.iterator();
                   while(it2.hasNext()) {
                       KeYJavaType guardKjt = it2.next();
                       if(containingKjt.equals(guardKjt)) {
                           clause = clause.remove(loc);
                       }
                   }
               }
           }
       }
       
       return clause;
    }
    
    
    /**
     * Compares two sets of location descriptors
     * (helper for getDependsClauseForInv()).
     */
    private boolean equalsModRenaming(SetOfLocationDescriptor locs1, 
                                      SetOfLocationDescriptor locs2) {
        if(locs1.size() != locs2.size()) {
            return false;
        }
        
        Function pred = new RigidFunction(new Name(""), 
                                          Sort.FORMULA, 
                                          new Sort[] {Sort.ANY});
        
        IteratorOfLocationDescriptor it1 = locs1.iterator();
        while(it1.hasNext()) {
            LocationDescriptor loc1 = it1.next();
            if(!(loc1 instanceof BasicLocationDescriptor)) {
                continue;
            }
            BasicLocationDescriptor bloc1 = (BasicLocationDescriptor) loc1;
            
            Term predLoc1Term = TF.createFunctionTerm(pred, 
                                                      bloc1.getLocTerm());
            Term freeLoc1Term = TF.createJunctorTerm(Junctor.AND, 
                                                     bloc1.getFormula(), 
                                                     predLoc1Term); 
            Term boundLoc1Term 
                = TF.createQuantifierTerm(Op.ALL, 
                                          freeLoc1Term.freeVars().toArray(), 
                                          freeLoc1Term);
            
            IteratorOfLocationDescriptor it2 = locs2.iterator();
            boolean found = false;
            while(it2.hasNext()) {
                LocationDescriptor loc2 = it2.next();
                if(!(loc2 instanceof BasicLocationDescriptor)) {
                    continue;
                }
                BasicLocationDescriptor bloc2 = (BasicLocationDescriptor) loc2;
                
                Term predLoc2Term = TF.createFunctionTerm(pred, 
                                                          bloc2.getLocTerm());
                Term freeLoc2Term = TF.createJunctorTerm(Junctor.AND, 
                                                         bloc2.getFormula(), 
                                                         predLoc2Term); 
                Term boundLoc2Term 
                    = TF.createQuantifierTerm(Op.ALL, 
                                              freeLoc2Term.freeVars().toArray(), 
                                              freeLoc2Term);
                
                if(boundLoc1Term.equalsModRenaming(boundLoc2Term)) {
                    locs2 = locs2.remove(loc2);
                    found = true;
                    break;
                }
            }
            
            if(!found) {
                return false;
            }
        }
        
        return locs2.size() == 0;
    }
    
    
    
    /**
     * Determines a depends clause for an invariant
     * (helper for buildEncapsulationFormula).
     */
    private SetOfLocationDescriptor getDependsClauseForInv(ClassInvariant inv) 
    		throws ProofInputException {
        Term invTerm = null;
        
        invTerm = translateInv(inv);
        
        SetOfLocationDescriptor extractedClause 
                = extractDependsClauseFromTerm(invTerm);
        extractedClause = filterDependsClause(extractedClause);
        
        DependsClauseDialog dlg = new DependsClauseDialog(inv, 
                                                          initConfig, 
                                                          extractedClause);
        SetOfLocationDescriptor result = extractedClause;
        if(dlg.wasSuccessful()) {
            result = dlg.getDependsClause();
            
            if(!equalsModRenaming(result, extractedClause)) {
                ProofOblInput dependsPO = new CorrectDependsPO(initConfig, 
                					       result, 
                					       inv);
                dependsPOs = dependsPOs.prepend(dependsPO);
            }
        }
        
        return result;
    }
    
        
    private Term createInstanceOf(KeYJavaType kjt, Term term) {
        Name n = new Name(kjt.getFullName() + "::instance");
        Function instanceFunc = (Function) initConfig.funcNS().lookup(n);
        Term instanceTerm = TB.func(instanceFunc, term);
        return TB.equals(instanceTerm, TB.TRUE(services));
    }
    
    
    /**
     * Creates the proof obligation's main formula and saves it in a field.
     */
    private void buildEncapsulationFormula() throws ProofInputException {
        if(encapsulationFormula != null) {
            return;
        }
        
        Sort javaLangObjectSort = javaInfo.getJavaLangObjectAsSort();
        Function accPred = getAccPred();
        
        //get a depends clause
        SetOfLocationDescriptor dependsClause 
                = SetAsListOfLocationDescriptor.EMPTY_SET;
        IteratorOfClassInvariant it = guardedInvs.iterator();
        while(it.hasNext()) {
            ClassInvariant inv = it.next();
            dependsClause = dependsClause.union(getDependsClauseForInv(inv));
        }
        
        //create the formula
        encapsulationFormula = TF.createJunctorTerm(Junctor.TRUE);
        IteratorOfLocationDescriptor it2 = dependsClause.iterator();
        while(it2.hasNext()) {
            LocationDescriptor loc = it2.next();
            Debug.assertTrue(loc instanceof BasicLocationDescriptor);
            BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;
            
            if(bloc.getLocTerm().arity() == 0) {
                continue;
            }
            
            LogicVariable y = new LogicVariable(new Name("y"), 
                                                javaLangObjectSort);
            Term yTerm = TF.createVariableTerm(y);
            Term dTerm = bloc.getLocTerm().sub(0);
            Term phiTerm = bloc.getFormula();

            //create "Acc(y, d_k') & phi_k"
            Term accTerm = TF.createFunctionTerm(accPred, 
                                                 yTerm,
                                                 dTerm);
            Term premiseTerm = TF.createJunctorTermAndSimplify(Junctor.AND, 
                                                               accTerm, 
                                                               phiTerm);
            
            //create disjunction of "C::Instance(y)" for all guards C
            Term isGuardTerm = TF.createJunctorTerm(Junctor.FALSE);
            IteratorOfKeYJavaType it3 = guard.iterator();
            while(it3.hasNext()) {
                KeYJavaType guardKJT = it3.next();
                Term instanceOfTerm = createInstanceOf(guardKJT, yTerm);
                isGuardTerm 
                    = TF.createJunctorTermAndSimplify(Junctor.OR, 
                                                      isGuardTerm, 
                                                      instanceOfTerm);
            }

            //create "phi_k & y = d_k'"  
            Term yEqualTerm = TF.createEqualityTerm(yTerm, dTerm);
            Term isWithinTerm = TF.createJunctorTermAndSimplify(Junctor.AND, 
                                                                phiTerm, 
                                                                yEqualTerm);
            
            //create implication
            Term impTerm 
                = TF.createJunctorTerm(Junctor.IMP,
                                       premiseTerm,
                                       TF.createJunctorTerm(Junctor.OR, 
                                                            isWithinTerm, 
                                                            isGuardTerm));
            
            //create quantification
            Term quantifierTerm =
                CreatedAttributeTermFactory.INSTANCE
                                           .createCreatedNotNullQuantifierTerm(
                             services, 
                             Op.ALL, 
                             new LogicVariable[] {y}, 
                             impTerm);
            SetOfQuantifiableVariable freeVars 
                    = bloc.getLocTerm().freeVars();
            quantifierTerm = (freeVars.size() == 0
                              ? quantifierTerm
                              : TF.createQuantifierTerm(Op.ALL, 
                                                        freeVars.toArray(), 
                                                        quantifierTerm));
            
            encapsulationFormula 
                    = TF.createJunctorTermAndSimplify(Junctor.AND, 
                                                      encapsulationFormula, 
                                                      quantifierTerm);
        } 
    }
    
    
    /**
     * Creates the term "ex x. Acc(x, v)".
     */
    private Term createAccessedTerm(ProgramVariable v, 
                                    Sort javaLangObjectSort, 
                                    Function accPred) {
        LogicVariable x = new LogicVariable(new Name("x"), 
                                            javaLangObjectSort);
        Term accTerm = TF.createFunctionTerm(accPred, 
                                             TF.createVariableTerm(x), 
                                             TF.createVariableTerm(v));
        return TF.createQuantifierTerm(Op.EX, x, accTerm);
    }
    
    
    protected Term getPreTerm(ProgramVariable selfVar, 
                              ListOfProgramVariable paramVars, 
                              ProgramVariable resultVar,
                              ProgramVariable exceptionVar,
                              Map<Operator, Function/*atPre*/> atPreFunctions) throws ProofInputException {
        Term result = TF.createJunctorTerm(Junctor.TRUE);
        Function accPred = getAccPred();
        Sort javaLangObjectSort = javaInfo.getJavaLangObjectAsSort();
        
        //create and conjoin "ex x . Acc(x, p)" for all parameters p of an 
        //object sort
        for (final ProgramVariable paramVar : paramVars) {
            Term paramAccTerm = createAccessedTerm(paramVar,
                                                   javaLangObjectSort, 
                                                   accPred);
            result = TF.createJunctorTermAndSimplify(Junctor.AND, 
                                                     result, 
                                                     paramAccTerm);
        }
        
        //add "ex x . Acc(x, self)"
        if(selfVar != null) {
            Term selfAccTerm = createAccessedTerm(selfVar, 
                                                  javaLangObjectSort, 
                                                  accPred); 
            result = TF.createJunctorTermAndSimplify(Junctor.AND, 
                                                     result, 
                                                     selfAccTerm);
        }
        
        //add main formula
        buildEncapsulationFormula();
        result = TF.createJunctorTermAndSimplify(Junctor.AND, 
                                                 result, 
                                                 encapsulationFormula);
        
        return result;
    }
    
    
    protected Term getPostTerm(ProgramVariable selfVar, 
                               ListOfProgramVariable paramVars, 
                               ProgramVariable resultVar,
                               ProgramVariable exceptionVar,
                               Map<Operator, Function/*atPre*/> atPreFunctions) throws ProofInputException {
        Term result = TF.createJunctorTerm(Junctor.TRUE);
        Function accPred = getAccPred();
        Sort javaLangObjectSort = javaInfo.getJavaLangObjectAsSort();

        //create "ex x . Acc(x, result)"
        if(resultVar != null) {
            result = createAccessedTerm(resultVar, javaLangObjectSort, accPred); 
        }
        
        //add main formula
        buildEncapsulationFormula();
        result = TF.createJunctorTermAndSimplify(Junctor.IMP, 
                                                 result, 
                                                 encapsulationFormula);
        
        return result;
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------    
    
    public void readProblem(ModStrategy mod) throws ProofInputException {
        super.readProblem(mod);
        
        Debug.assertTrue(poTerms.length == 1);
        Debug.assertTrue(poNames == null);
        Term poTerm = poTerms[0];
        
        int numPOs = 1 + dependsPOs.size();
        poTerms = new Term[numPOs];
        poNames = new String[numPOs];
        poTerms[0] = poTerm;
        poNames[0] = name();
        
        IteratorOfProofOblInput it = dependsPOs.iterator();
        int i = 1;
        while(it.hasNext()) {
            CorrectDependsPO dependsPO = ((CorrectDependsPO) it.next());
            dependsPO.readProblem(mod);
            poTerms[i] = dependsPO.getTerm();
            poNames[i] = dependsPO.name();
            i++;
        }
    }
    
    
    public boolean equals(Object o) {
        if(!(o instanceof PreservesGuardPO)) {
            return false;
        }
        PreservesGuardPO po = (PreservesGuardPO) o;
        return super.equals(po)
               && guardedInvs.equals(po.guardedInvs)
               && guard.equals(po.guard);
    }
    
    
    public int hashCode() {
        return super.hashCode() + guardedInvs.hashCode() + guard.hashCode();
    }
}
