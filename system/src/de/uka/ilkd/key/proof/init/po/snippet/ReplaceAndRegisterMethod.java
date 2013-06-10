/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.StateVars;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.util.InfFlowSpec;
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
        Term intermediateResult = replace(term, origVars.pre, poVars.pre);
        return replace(intermediateResult, origVars.post, poVars.post);
    }


    final Term replace(Term term,
                       StateVars origVars,
                       StateVars poVars) {
        de.uka.ilkd.key.util.LinkedHashMap<Term, Term> map =
                new de.uka.ilkd.key.util.LinkedHashMap<Term, Term>();

        Iterator<Term> origVarsIt;
        Iterator<Term> poVarsIt;
        assert origVars.paddedTermList.size() ==
               poVars.paddedTermList.size();
        origVarsIt = origVars.paddedTermList.iterator();
        poVarsIt = poVars.paddedTermList.iterator();
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
        OpReplacer or = new OpReplacer(map);
        Term result = or.replace(term);

        return result;
    }


    final Term[] replace(Term[] terms,
                         StateVars origVars,
                         StateVars poVars) {
        final Term[] result = new Term[terms.length];
        for (int i = 0; i < terms.length; i++) {
            result[i] = replace(terms[i], origVars, poVars);

        }
        return result;
    }


    final InfFlowSpec replace(InfFlowSpec terms,
                              StateVars origVars,
                              StateVars poVars) {
        ImmutableList<Term> resultSeparates = ImmutableSLList.<Term>nil();
        for (Term t : terms.separates) {
            resultSeparates = resultSeparates.append(replace(t, origVars, poVars));
        }
        ImmutableList<Term> resultDeclassifies = ImmutableSLList.<Term>nil();
        for (Term t : terms.declassifies) {
            resultDeclassifies = resultDeclassifies.append(replace(t, origVars, poVars));
        }
        ImmutableList<Term> resultErases = ImmutableSLList.<Term>nil();
        for (Term t : terms.erases) {
            resultErases = resultErases.append(replace(t, origVars, poVars));
        }
        ImmutableList<Term> resultNewObjecs = ImmutableSLList.<Term>nil();
        for (Term t : terms.newObjects) {
            resultErases = resultErases.append(replace(t, origVars, poVars));
        }
        return new InfFlowSpec(resultSeparates, resultDeclassifies,
                               resultErases, resultNewObjecs);
    }


    final InfFlowSpec[] replace(ImmutableList<InfFlowSpec> termss,
                                StateVars origVars,
                                StateVars poVars) {
        final InfFlowSpec[] result = new InfFlowSpec[termss.size()];
        Iterator<InfFlowSpec> it = termss.iterator();
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
