// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
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

import de.uka.ilkd.key.casetool.IteratorOfModelClass;
import de.uka.ilkd.key.casetool.ListOfModelClass;
import de.uka.ilkd.key.casetool.ModelClass;
import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.gui.DependsClauseDialog;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.IteratorOfClassInvariant;
import de.uka.ilkd.key.speclang.ListOfClassInvariant;
import de.uka.ilkd.key.speclang.SLTranslationError;
import de.uka.ilkd.key.util.Debug;


/**
 * The "PreservesGuard" proof obligation.
 */
public class PreservesGuardPO extends EnsuresPO {
    
    private final ListOfClassInvariant guardedInvs;
    private final ListOfModelClass guard;
    private Term encapsulationFormula = null;
    private ListOfProofOblInput dependsPOs = SLListOfProofOblInput.EMPTY_LIST;

    
    public PreservesGuardPO(ModelMethod modelMethod, 
                            ListOfClassInvariant guardedInvs,
                            ListOfModelClass guard,
                            InvariantSelectionStrategy invStrategy) {
        super("PreservesGuard", 
              modelMethod, 
              Op.BOX, 
              invStrategy, 
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
               } else if (op instanceof AttributeOp) {
                   AttributeOp aop = (AttributeOp) op;
                   if(aop.attribute() instanceof ProgramVariable) {
                       containingKjt 
                           = ((ProgramVariable) aop.attribute())
                             .getContainerType();
                   }
               }
               
               if(containingKjt != null) {
                   IteratorOfModelClass it2 = guard.iterator();
                   while(it2.hasNext()) {
                       ModelClass guardClass = it2.next();
                       KeYJavaType guardKjt 
                           = javaInfo.getKeYJavaType(guardClass.getFullClassName());
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
            
            Term predLoc1Term = tf.createFunctionTerm(pred, 
                                                      bloc1.getLocTerm());
            Term freeLoc1Term = tf.createJunctorTerm(Op.AND, 
                                                     bloc1.getFormula(), 
                                                     predLoc1Term); 
            Term boundLoc1Term 
                = tf.createQuantifierTerm(Op.ALL, 
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
                
                Term predLoc2Term = tf.createFunctionTerm(pred, 
                                                          bloc2.getLocTerm());
                Term freeLoc2Term = tf.createJunctorTerm(Op.AND, 
                                                         bloc2.getFormula(), 
                                                         predLoc2Term); 
                Term boundLoc2Term 
                    = tf.createQuantifierTerm(Op.ALL, 
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
    private SetOfLocationDescriptor getDependsClauseForInv(ClassInvariant inv) {
        Term invTerm = null;
        
    	try {
        	invTerm = translateInv(inv);
        } catch (SLTranslationError e) {        	
            e.printStackTrace();
        }
        
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
                ProofOblInput dependsPO = new CorrectDependsPO(result, inv);
                dependsPOs = dependsPOs.prepend(dependsPO);
            }
        }
        
        return result;
    }
    
        
    private Term createInstanceOf(ModelClass modelClass, Term term) {
        Name name = new Name(modelClass.getFullClassName() + "::instance");
        Function instanceFunc = (Function) initConfig.funcNS().lookup(name);
        Term instanceTerm = tf.createFunctionTerm(instanceFunc, term);
        Term trueLitTerm = services.getTypeConverter()
                                   .convertToLogicElement(BooleanLiteral.TRUE);
        return tf.createEqualityTerm(instanceTerm, trueLitTerm);
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
        encapsulationFormula = tf.createJunctorTerm(Op.TRUE);
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
            Term yTerm = tf.createVariableTerm(y);
            Term dTerm = bloc.getLocTerm().sub(0);
            Term phiTerm = bloc.getFormula();

            //create "Acc(y, d_k') & phi_k"
            Term accTerm = tf.createFunctionTerm(accPred, 
                                                 yTerm,
                                                 dTerm);
            Term premiseTerm = tf.createJunctorTermAndSimplify(Op.AND, 
                                                               accTerm, 
                                                               phiTerm);
            
            //create disjunction of "C::Instance(y)" for all guards C
            Term isGuardTerm = tf.createJunctorTerm(Op.FALSE);
            IteratorOfModelClass it3 = guard.iterator();
            while(it3.hasNext()) {
                ModelClass guardClass = it3.next();
                Term instanceOfTerm = createInstanceOf(guardClass, yTerm);
                isGuardTerm 
                    = tf.createJunctorTermAndSimplify(Op.OR, 
                                                      isGuardTerm, 
                                                      instanceOfTerm);
            }

            //create "phi_k & y = d_k'"  
            Term yEqualTerm = tf.createEqualityTerm(yTerm, dTerm);
            Term isWithinTerm = tf.createJunctorTermAndSimplify(Op.AND, 
                                                                phiTerm, 
                                                                yEqualTerm);
            
            //create implication
            Term impTerm 
                = tf.createJunctorTerm(Op.IMP,
                                       premiseTerm,
                                       tf.createJunctorTerm(Op.OR, 
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
                              : tf.createQuantifierTerm(Op.ALL, 
                                                        freeVars.toArray(), 
                                                        quantifierTerm));
            
            encapsulationFormula 
                    = tf.createJunctorTermAndSimplify(Op.AND, 
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
        Term accTerm = tf.createFunctionTerm(accPred, 
                                             tf.createVariableTerm(x), 
                                             tf.createVariableTerm(v));
        return tf.createQuantifierTerm(Op.EX, x, accTerm);
    }
    
    
    protected Term getPreTerm(ProgramVariable selfVar, 
                              ListOfProgramVariable paramVars, 
                              ProgramVariable resultVar,
                              ProgramVariable exceptionVar,
                              Map atPreFunctions) throws ProofInputException {
        Term result = tf.createJunctorTerm(Op.TRUE);
        Function accPred = getAccPred();
        Sort javaLangObjectSort = javaInfo.getJavaLangObjectAsSort();
        
        //create and conjoin "ex x . Acc(x, p)" for all parameters p of an 
        //object sort
        IteratorOfProgramVariable it = paramVars.iterator();
        while(it.hasNext()) {
            ProgramVariable paramVar = it.next();
            Term paramAccTerm = createAccessedTerm(paramVar,
                                                   javaLangObjectSort, 
                                                   accPred);
            result = tf.createJunctorTermAndSimplify(Op.AND, 
                                                     result, 
                                                     paramAccTerm);
        }
        
        //add "ex x . Acc(x, self)"
        if(selfVar != null) {
            Term selfAccTerm = createAccessedTerm(selfVar, 
                                                  javaLangObjectSort, 
                                                  accPred); 
            result = tf.createJunctorTermAndSimplify(Op.AND, 
                                                     result, 
                                                     selfAccTerm);
        }
        
        //add main formula
        buildEncapsulationFormula();
        result = tf.createJunctorTermAndSimplify(Op.AND, 
                                                 result, 
                                                 encapsulationFormula);
        
        return result;
    }
    
    
    protected Term getPostTerm(ProgramVariable selfVar, 
                               ListOfProgramVariable paramVars, 
                               ProgramVariable resultVar,
                               ProgramVariable exceptionVar,
                               Map atPreFunctions) throws ProofInputException {
        Term result = tf.createJunctorTerm(Op.TRUE);
        Function accPred = getAccPred();
        Sort javaLangObjectSort = javaInfo.getJavaLangObjectAsSort();

        //create "ex x . Acc(x, result)"
        if(resultVar != null) {
            result = createAccessedTerm(resultVar, javaLangObjectSort, accPred); 
        }
        
        //add main formula
        buildEncapsulationFormula();
        result = tf.createJunctorTermAndSimplify(Op.IMP, 
                                                 result, 
                                                 encapsulationFormula);
        
        return result;
    }
    
    
    
    //-------------------------------------------------------------------------
    //methods of ProofOblInput interface
    //-------------------------------------------------------------------------    
    
    public void readProblem(ModStrategy mod) throws ProofInputException {
        super.readProblem(mod);
        setInitConfig(initConfig);
        
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
        }
    }

    
    public void setInitConfig(InitConfig conf) {
        super.setInitConfig(conf);
        IteratorOfProofOblInput it = dependsPOs.iterator();
        while(it.hasNext()) {
            it.next().setInitConfig(conf);
        }
    }
}
