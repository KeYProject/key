// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.AtPreFactory;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class AtPreEquations extends AbstractMetaOperator {

    private static Term updateFormula = null;
    private static HashMap atPreMapping = null;
    
    public static Map getAtPreFunctions(Term t, Services services){
        if(t==updateFormula){
            // atPre Functions were already calculated for updateFormula
            return atPreMapping;
        }
        updateFormula = t;
        atPreMapping = new HashMap();
        AtPreFactory.INSTANCE.createAtPreFunctionsForTerm(t, atPreMapping, services);
        return atPreMapping;
    }
    
    /**
     * Helper for buildAtPreDefinitions().
     */
    private static Term[] getTerms(ArrayOfQuantifiableVariable vars) {
        int numVars = vars.size();
        Term[] result = new Term[numVars];

        for(int i = 0; i < numVars; i++) {
            LogicVariable var
                    = (LogicVariable)(vars.getQuantifiableVariable(i));
            result[i] = TermBuilder.DF.var(var);
        }

        return result;
    }
    
    /**
     * @deprecated use updates for defining atPre-functions instead.
     */
    private static Term buildAtPreDefinitions(
                        /*in*/ Map /*Operator -> Function */atPreFunctions) {
        Term result = TermBuilder.DF.tt();

        Iterator it = atPreFunctions.entrySet().iterator();
        while(it.hasNext()) {
            Map.Entry entry = (Map.Entry)(it.next());
            Operator f1 = (Operator)(entry.getKey());
            Function f2 = (Function)(entry.getValue());

            int arity = f1.arity();
            assert arity == f2.arity();
            LogicVariable[] args = new LogicVariable[arity];
            for(int i = 0; i < arity; i++) {
                args[i] = new LogicVariable(new Name("x" + i), f2.argSort(i));
            }

            Term[] argTerms = getTerms(new ArrayOfQuantifiableVariable(args));

            TermFactory tf = TermBuilder.DF.tf();
            Term f1Term = tf.createTerm(f1,   argTerms,
                                        null,
                                        null);
            Term f2Term = TermBuilder.DF.func(f2, argTerms);
            Term equalsTerm = tf.createJunctorTerm(Equality.EQUALS, f1Term, f2Term);
            Term quantifTerm;
            if(arity > 0) {
                quantifTerm = TermBuilder.DF.all(args, equalsTerm);
            } else {
                quantifTerm = equalsTerm;
            }
            result = TermBuilder.DF.and(result, quantifTerm);
        }

        return result;
    }
    
    
    public AtPreEquations() {
        super(new Name("#atPreEqs"), 1, Sort.FORMULA);
    }
    

    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        Map atPreFunctions = getAtPreFunctions(term.sub(0), services);
        return buildAtPreDefinitions(atPreFunctions);
    }
                


    public boolean isRigid(Term term) {
        return false;
    }    
}
