// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.proof.init.proofobligation;

import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.DependsClauseDialog;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.BasicLocationDescriptor;
import de.uka.ilkd.key.logic.LocationDescriptor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.util.Debug;


/**
 * The "PreservesGuard" proof obligation.
 */
public class PreservesGuardPO extends EnsuresPO {

    private static final QuantifiableVariable[] EMPTY_QV_ARRAY = new QuantifiableVariable[0];
    private final ImmutableSet<ClassInvariant> guardedInvs;
    private final ImmutableSet<KeYJavaType> guard;
    private Term encapsulationFormula = null;
    private ImmutableList<ProofOblInput> dependsPOs = ImmutableSLList.<ProofOblInput>nil();


    public PreservesGuardPO(InitConfig initConfig,
	    		    ProgramMethod programMethod,
                            ImmutableSet<ClassInvariant> guardedInvs,
                            ImmutableSet<KeYJavaType> guard) {
        super(initConfig,
              "PreservesGuard (" + programMethod + ")",
              programMethod,
              Op.BOX,
              DefaultImmutableSet.<ClassInvariant>nil(),
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
    private ImmutableSet<LocationDescriptor> extractDependsClauseFromTerm(Term term) {
        ImmutableSet<LocationDescriptor> result
                = DefaultImmutableSet.<LocationDescriptor>nil();

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
    private ImmutableSet<LocationDescriptor> filterDependsClause(
                                            ImmutableSet<LocationDescriptor> clause) {
        for (LocationDescriptor aClause : clause) {
            LocationDescriptor loc = aClause;

            if (loc instanceof BasicLocationDescriptor) {
                Operator op = ((BasicLocationDescriptor) loc).getLocTerm().op();

                KeYJavaType containingKjt = null;
                if (op instanceof ProgramVariable) {
                    containingKjt
                            = ((ProgramVariable) op).getContainerType();
                } else if (op instanceof AttributeOp) {
                    AttributeOp aop = (AttributeOp) op;
                    if (aop.attribute() instanceof ProgramVariable) {
                        containingKjt
                                = ((ProgramVariable) aop.attribute())
                                .getContainerType();
                    }
                }

                if (containingKjt != null) {
                    for (KeYJavaType aGuard : guard) {
                        KeYJavaType guardKjt = aGuard;
                        if (containingKjt.equals(guardKjt)) {
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
    private boolean equalsModRenaming(ImmutableSet<LocationDescriptor> locs1,
                                      ImmutableSet<LocationDescriptor> locs2) {
        if(locs1.size() != locs2.size()) {
            return false;
        }

        Function pred = new RigidFunction(new Name(""),
                                          Sort.FORMULA,
                                          new Sort[] {Sort.ANY});

        for (LocationDescriptor aLocs1 : locs1) {
            LocationDescriptor loc1 = aLocs1;
            if (!(loc1 instanceof BasicLocationDescriptor)) {
                continue;
            }
            BasicLocationDescriptor bloc1 = (BasicLocationDescriptor) loc1;

            Term predLoc1Term = TF.createFunctionTerm(pred,
                    bloc1.getLocTerm());
            Term freeLoc1Term = TF.createJunctorTerm(Op.AND,
                    bloc1.getFormula(),
                    predLoc1Term);
            Term boundLoc1Term
                    = TF.createQuantifierTerm(Op.ALL,
                    freeLoc1Term.freeVars().toArray(EMPTY_QV_ARRAY),
                    freeLoc1Term);

            Iterator<LocationDescriptor> it2 = locs2.iterator();
            boolean found = false;
            while (it2.hasNext()) {
                LocationDescriptor loc2 = it2.next();
                if (!(loc2 instanceof BasicLocationDescriptor)) {
                    continue;
                }
                BasicLocationDescriptor bloc2 = (BasicLocationDescriptor) loc2;

                Term predLoc2Term = TF.createFunctionTerm(pred,
                        bloc2.getLocTerm());
                Term freeLoc2Term = TF.createJunctorTerm(Op.AND,
                        bloc2.getFormula(),
                        predLoc2Term);
                Term boundLoc2Term
                        = TF.createQuantifierTerm(Op.ALL,
                        freeLoc2Term.freeVars().toArray(EMPTY_QV_ARRAY),
                        freeLoc2Term);

                if (boundLoc1Term.equalsModRenaming(boundLoc2Term)) {
                    locs2 = locs2.remove(loc2);
                    found = true;
                    break;
                }
            }

            if (!found) {
                return false;
            }
        }

        return locs2.size() == 0;
    }



    /**
     * Determines a depends clause for an invariant
     * (helper for buildEncapsulationFormula).
     */
    private ImmutableSet<LocationDescriptor> getDependsClauseForInv(ClassInvariant inv)
    		throws ProofInputException {
        Term invTerm = null;

        invTerm = translateInv(inv);

        ImmutableSet<LocationDescriptor> extractedClause
                = extractDependsClauseFromTerm(invTerm);
        extractedClause = filterDependsClause(extractedClause);

        DependsClauseDialog dlg = new DependsClauseDialog(inv,
                                                          initConfig,
                                                          extractedClause);
        ImmutableSet<LocationDescriptor> result = extractedClause;
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
        ImmutableSet<LocationDescriptor> dependsClause
                = DefaultImmutableSet.<LocationDescriptor>nil();
        for (ClassInvariant guardedInv : guardedInvs) {
            ClassInvariant inv = guardedInv;
            dependsClause = dependsClause.union(getDependsClauseForInv(inv));
        }

        //create the formula
        encapsulationFormula = TF.createJunctorTerm(Op.TRUE);
        for (LocationDescriptor aDependsClause : dependsClause) {
            LocationDescriptor loc = aDependsClause;
            Debug.assertTrue(loc instanceof BasicLocationDescriptor);
            BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;

            if (bloc.getLocTerm().arity() == 0) {
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
            Term premiseTerm = TF.createJunctorTermAndSimplify(Op.AND,
                    accTerm,
                    phiTerm);

            //create disjunction of "C::Instance(y)" for all guards C
            Term isGuardTerm = TF.createJunctorTerm(Op.FALSE);
            for (KeYJavaType aGuard : guard) {
                KeYJavaType guardKJT = aGuard;
                Term instanceOfTerm = createInstanceOf(guardKJT, yTerm);
                isGuardTerm
                        = TF.createJunctorTermAndSimplify(Op.OR,
                        isGuardTerm,
                        instanceOfTerm);
            }

            //create "phi_k & y = d_k'"
            Term yEqualTerm = TF.createEqualityTerm(yTerm, dTerm);
            Term isWithinTerm = TF.createJunctorTermAndSimplify(Op.AND,
                    phiTerm,
                    yEqualTerm);

            //create implication
            Term impTerm
                    = TF.createJunctorTerm(Op.IMP,
                    premiseTerm,
                    TF.createJunctorTerm(Op.OR,
                            isWithinTerm,
                            isGuardTerm));

            //create quantification
            Term quantifierTerm =
                    CreatedAttributeTermFactory.INSTANCE
                            .createCreatedNotNullQuantifierTerm(
                                    services,
                                    Op.ALL,
                                    new LogicVariable[]{y},
                                    impTerm);
            ImmutableSet<QuantifiableVariable> freeVars
                    = bloc.getLocTerm().freeVars();
            quantifierTerm = (freeVars.size() == 0
                    ? quantifierTerm
                    : TF.createQuantifierTerm(Op.ALL,
                    freeVars.toArray(EMPTY_QV_ARRAY),
                    quantifierTerm));

            encapsulationFormula
                    = TF.createJunctorTermAndSimplify(Op.AND,
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
                              ImmutableList<ProgramVariable> paramVars,
                              ProgramVariable resultVar,
                              ProgramVariable exceptionVar,
                              Map<Operator, Function/*atPre*/> atPreFunctions) throws ProofInputException {
        Term result = TF.createJunctorTerm(Op.TRUE);
        Function accPred = getAccPred();
        Sort javaLangObjectSort = javaInfo.getJavaLangObjectAsSort();

        //create and conjoin "ex x . Acc(x, p)" for all parameters p of an
        //object sort
        for (final ProgramVariable paramVar : paramVars) {
            Term paramAccTerm = createAccessedTerm(paramVar,
                                                   javaLangObjectSort,
                                                   accPred);
            result = TF.createJunctorTermAndSimplify(Op.AND,
                                                     result,
                                                     paramAccTerm);
        }

        //add "ex x . Acc(x, self)"
        if(selfVar != null) {
            Term selfAccTerm = createAccessedTerm(selfVar,
                                                  javaLangObjectSort,
                                                  accPred);
            result = TF.createJunctorTermAndSimplify(Op.AND,
                                                     result,
                                                     selfAccTerm);
        }

        //add main formula
        buildEncapsulationFormula();
        result = TF.createJunctorTermAndSimplify(Op.AND,
                                                 result,
                                                 encapsulationFormula);

        return result;
    }


    protected Term getPostTerm(ProgramVariable selfVar,
                               ImmutableList<ProgramVariable> paramVars,
                               ProgramVariable resultVar,
                               ProgramVariable exceptionVar,
                               Map<Operator, Function/*atPre*/> atPreFunctions) throws ProofInputException {
        Term result = TF.createJunctorTerm(Op.TRUE);
        Function accPred = getAccPred();
        Sort javaLangObjectSort = javaInfo.getJavaLangObjectAsSort();

        //create "ex x . Acc(x, result)"
        if(resultVar != null) {
            result = createAccessedTerm(resultVar, javaLangObjectSort, accPred);
        }

        //add main formula
        buildEncapsulationFormula();
        result = TF.createJunctorTermAndSimplify(Op.IMP,
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

        Iterator<ProofOblInput> it = dependsPOs.iterator();
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
