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
import de.uka.ilkd.key.util.Triple;
import java.util.Iterator;


/**
 * Generate term "self != null".
 * <p/>
 * @author christoph
 */
abstract class ReplaceAndRegisterMethod {

    final Term replace(Term term,
                       ProofObligationVars origVars,
                       ProofObligationVars poVars) {
        de.uka.ilkd.key.util.LinkedHashMap<Term, Term> map =
                new de.uka.ilkd.key.util.LinkedHashMap<Term, Term>();

        Iterator<Term> origVarsIt;
        Iterator<Term> poVarsIt;
        if (origVars.localIns.isEmpty() && origVars.localOuts.isEmpty()) {
            assert origVars.paddedTermListWithoutLocalVars.size() ==
                   poVars.paddedTermListWithoutLocalVars.size();
            origVarsIt = origVars.paddedTermListWithoutLocalVars.iterator();
            poVarsIt = poVars.paddedTermListWithoutLocalVars.iterator();
        } else {
            assert origVars.paddedTermList.size() ==
                   poVars.paddedTermList.size();
            origVarsIt = origVars.paddedTermList.iterator();
            poVarsIt = poVars.paddedTermList.iterator();
        }
        while (origVarsIt.hasNext()) {
            Term origTerm = origVarsIt.next();
            Term poTerm = poVarsIt.next();
            if (origTerm != null && poTerm != null) {
                assert poTerm.sort().equals(origTerm.sort()) ||
                       poTerm.sort().extendsSorts().contains(origTerm.sort()) :
                        "mismatch of sorts: orignal term " + origTerm +
                        ", sort " + origTerm.sort() +
                        "; replacement term" + poTerm + ", sort " +
                        poTerm.sort();
                map.put(origTerm, poTerm);
            }
        }
        System.out.println("RaR-map:" + map.toString()); // TODO: for debugging, to be removed
        System.out.println("RaR-term:" + term.toString()); // TODO: for debugging, to be removed
        OpReplacer or = new OpReplacer(map);
        Term result = or.replace(term);
        System.out.println("RaR-res:" + result.toString());

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


    final Triple<Term[], Term[], Term[]> replace(Triple<Term[], Term[], Term[]> terms,
                                       Term[] origVars,
                                       Term[] poVars) {
        final Term[] result1 = new Term[terms.first.length];
        for (int i = 0; i < terms.first.length; i++) {
            result1[i] = replace(terms.first[i], origVars, poVars);
        }
        final Term[] result2 = new Term[terms.second.length];
        for (int i = 0; i < terms.second.length; i++) {
            result2[i] = replace(terms.second[i], origVars, poVars);
        }
        final Term[] result3 = new Term[terms.third.length];
        for (int i = 0; i < terms.third.length; i++) {
            result3[i] = replace(terms.third[i], origVars, poVars);
        }
        return new Triple<Term[], Term[], Term[]>(result1, result2, result3);
    }


    final Triple<Term[], Term[], Term[]> replace(
            Triple<ImmutableList<Term>, ImmutableList<Term>, ImmutableList<Term>> terms,
            ProofObligationVars origVars,
            ProofObligationVars poVars) {
        final Term[] result1 = new Term[terms.first.size()];
        Iterator<Term> termIt1 = terms.first.iterator();
        for (int i = 0; termIt1.hasNext(); i++) {
            result1[i] = replace(termIt1.next(), origVars, poVars);
        }
        final Term[] result2 = new Term[terms.second.size()];
        Iterator<Term> termIt2 = terms.second.iterator();
        for (int i = 0; termIt2.hasNext(); i++) {
            result2[i] = replace(termIt2.next(), origVars, poVars);
        }
        final Term[] result3 = new Term[terms.third.size()];
        Iterator<Term> termIt3 = terms.third.iterator();
        for (int i = 0; termIt3.hasNext(); i++) {
            result3[i] = replace(termIt3.next(), origVars, poVars);
        }
        return new Triple<Term[], Term[], Term[]>(result1, result2, result3);
    }


    final Triple<Term[], Term[], Term[]>[] replace(Triple<Term[], Term[], Term[]>[] termss,
                                         Term[] origVars,
                                         Term[] poVars) {
        final Triple<Term[], Term[], Term[]>[] result = new Triple[termss.length];
        for (int i = 0; i < termss.length; i++) {
            result[i] = replace(termss[i], origVars, poVars);
        }
        return result;
    }


    final Triple<Term[], Term[], Term[]>[] replace(
            ImmutableList<Triple<ImmutableList<Term>, ImmutableList<Term>,
                                 ImmutableList<Term>>> termss,
            ProofObligationVars origVars,
            ProofObligationVars poVars) {
        final Triple<Term[], Term[], Term[]>[] result = new Triple[termss.size()];
        Iterator<Triple<ImmutableList<Term>, ImmutableList<Term>, ImmutableList<Term>>> it =
                termss.iterator();
        for (int i = 0; it.hasNext(); i++) {
            result[i] = replace(it.next(), origVars, poVars);
        }
        return result;
    }


    final Term replace(Term term,
                       Term[] origVars,
                       Term[] poVars) {
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


    final Term[] replace(Term[] terms,
                         Term[] origVars,
                         Term[] poVars) {
        final Term[] result = new Term[terms.length];
        for (int i = 0; i < terms.length; i++) {
            result[i] = replace(terms[i], origVars, poVars);

        }
        return result;
    }


    final Term[][] replace(Term[][] termss,
                           Term[] origVars,
                           Term[] poVars) {
        final Term[][] result = new Term[termss.length][];
        for (int i = 0; i < termss.length; i++) {
            result[i] = replace(termss[i], origVars, poVars);
        }
        return result;
    }


    final void register(ProgramVariable pv,
                        Services services) {
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


    final void register(Function f,
                        Services services) {
        Namespace functionNames = services.getNamespaces().functions();
        if (f != null && functionNames.lookup(f.name()) == null) {
            assert f.sort() != Sort.UPDATE;
            functionNames.addSafely(f);
        }
    }
}
