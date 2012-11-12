/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import java.util.Iterator;

    
/**
 * Generate term "self != null".
 * 
 * @author christoph
 */
abstract class ReplaceAnRegisterMethod {

    final Term replace(Term term, ProofObligationVars origVars,
                       ProofObligationVars poVars) {
        de.uka.ilkd.key.util.LinkedHashMap<Term, Term> map =
                new de.uka.ilkd.key.util.LinkedHashMap<Term, Term>();
        
        assert origVars.termList.size() == poVars.termList.size();
        Iterator<Term> origVarsIt = origVars.termList.iterator();
        Iterator<Term> poVarsIt = poVars.termList.iterator();
        while (origVarsIt.hasNext()) {
            Term origTerm = origVarsIt.next();
            Term poTerm = poVarsIt.next();
            if (origTerm != null && poTerm != null) {
                assert origTerm.sort().equals(poTerm.sort());
                map.put(origTerm, poTerm);
            }
        }
        
        OpReplacer or = new OpReplacer(map);
        Term result = or.replace(term);
        
        return result;
    }
    

    final Term[] replace(Term[] terms,
                         ProofObligationVars origVars,
                         ProofObligationVars poVars) {
        final Term[] result = new Term[terms.length];
        for (int i = 0; i < terms.length; i++) {
            result[i] = replace(terms[i], origVars, poVars);

        }
        return result;
    }


    final Term[][] replace(Term[][] termss,
                           ProofObligationVars origVars,
                           ProofObligationVars poVars) {
        final Term[][] result = new Term[termss.length][];
        for (int i = 0; i < termss.length; i++) {
            result[i] = replace(termss[i], origVars, poVars);
        }
        return result;
    }

    
    final Term replace(Term term, Term[] origVars, Term[] poVars) {
        de.uka.ilkd.key.util.LinkedHashMap<Term, Term> map =
                new de.uka.ilkd.key.util.LinkedHashMap<Term, Term>();

        assert origVars.length == poVars.length;
        for (int i = 0; i < origVars.length; i++) {
            Term origTerm = origVars[i];
            Term poTerm = poVars[i];
            if (origTerm != null && poTerm != null) {
                assert origTerm.sort().equals(poTerm.sort());
                map.put(origTerm, poTerm);
            }
        }

        OpReplacer or = new OpReplacer(map);
        Term result = or.replace(term);

        return result;
    }


    final Term[] replace(Term[] terms, Term[] origVars, Term[] poVars) {
        final Term[] result = new Term[terms.length];
        for (int i = 0; i < terms.length; i++) {
            result[i] = replace(terms[i], origVars, poVars);

        }
        return result;
    }


    final Term[][] replace(Term[][] termss, Term[] origVars, Term[] poVars) {
        final Term[][] result = new Term[termss.length][];
        for (int i = 0; i < termss.length; i++) {
            result[i] = replace(termss[i], origVars, poVars);
        }
        return result;
    }


    final void register(ProgramVariable pv, Services services) {
        Namespace progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }

    
    final void register(ImmutableList<ProgramVariable> pvs,
                                  Services services) {
        for (ProgramVariable pv : pvs) {
            register(pv, services);
        }
    }

    
    final void register(Function f, Services services) {
        Namespace functionNames = services.getNamespaces().functions();
        if (f != null && functionNames.lookup(f.name()) == null) {
            assert f.sort() != Sort.UPDATE;
            functionNames.addSafely(f);
        }
    }

}
