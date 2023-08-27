/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import java.util.*;

import de.uka.ilkd.key.informationflow.proof.init.StateVars;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.LinkedHashMap;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;


/**
 * Generate term "self != null".
 * <p/>
 *
 * @author christoph
 */
abstract class ReplaceAndRegisterMethod {

    final Term replace(Term term, ProofObligationVars origVars, ProofObligationVars poVars,
            TermBuilder tb) {
        Term intermediateResult = replace(term, origVars.pre, poVars.pre, tb);
        return replace(intermediateResult, origVars.post, poVars.post, tb);
    }


    final Term replace(Term term, StateVars origVars, StateVars poVars, TermBuilder tb) {
        LinkedHashMap<Term, Term> map = new LinkedHashMap<>();

        Iterator<Term> origVarsIt;
        Iterator<Term> poVarsIt;
        assert origVars.paddedTermList.size() == poVars.paddedTermList.size();
        origVarsIt = origVars.paddedTermList.iterator();
        poVarsIt = poVars.paddedTermList.iterator();
        while (origVarsIt.hasNext()) {
            Term origTerm = origVarsIt.next();
            Term poTerm = poVarsIt.next();
            if (origTerm != null && poTerm != null) {
                assert poTerm.sort().equals(origTerm.sort())
                        || poTerm.sort().extendsSorts().contains(origTerm.sort())
                        : "mismatch of sorts: orignal term " + origTerm + ", sort "
                            + origTerm.sort() + "; replacement term" + poTerm + ", sort "
                            + poTerm.sort();
                map.put(origTerm, poTerm);
            }
        }
        OpReplacer or = new OpReplacer(map, tb.tf());
        return or.replace(term);
    }


    final Term[] replace(Term[] terms, StateVars origVars, StateVars poVars, TermBuilder tb) {
        final Term[] result = new Term[terms.length];
        for (int i = 0; i < terms.length; i++) {
            result[i] = replace(terms[i], origVars, poVars, tb);

        }
        return result;
    }


    final InfFlowSpec replace(InfFlowSpec terms, StateVars origVars, StateVars poVars,
            TermBuilder tb) {
        ImmutableList<Term> resultPreExps = ImmutableSLList.nil();
        for (Term t : terms.preExpressions) {
            resultPreExps = resultPreExps.append(replace(t, origVars, poVars, tb));
        }
        ImmutableList<Term> resultPostExps = ImmutableSLList.nil();
        for (Term t : terms.postExpressions) {
            resultPostExps = resultPostExps.append(replace(t, origVars, poVars, tb));
        }
        ImmutableList<Term> resultNewObjecs = ImmutableSLList.nil();
        for (Term t : terms.newObjects) {
            resultNewObjecs = resultNewObjecs.append(replace(t, origVars, poVars, tb));
        }
        return new InfFlowSpec(resultPreExps, resultPostExps, resultNewObjecs);
    }


    final InfFlowSpec[] replace(ImmutableList<InfFlowSpec> termss, StateVars origVars,
            StateVars poVars, TermBuilder tb) {
        final InfFlowSpec[] result = new InfFlowSpec[termss.size()];
        Iterator<InfFlowSpec> it = termss.iterator();
        for (int i = 0; it.hasNext(); i++) {
            result[i] = replace(it.next(), origVars, poVars, tb);
        }
        return result;
    }


    final Term replace(Term term, Term[] origVars, Term[] poVars, TermBuilder tb) {
        LinkedHashMap<Term, Term> map = new LinkedHashMap<>();

        assert origVars.length == poVars.length;
        for (int i = 0; i < origVars.length; i++) {
            Term origTerm = origVars[i];
            Term poTerm = poVars[i];
            if (origTerm != null && poTerm != null) {
                assert origTerm.sort().equals(poTerm.sort());
                map.put(origTerm, poTerm);
            }
        }

        OpReplacer or = new OpReplacer(map, tb.tf());
        Term result = or.replace(term);

        return result;
    }


    final void register(ProgramVariable pv, Services services) {
        Namespace<IProgramVariable> progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }


    final void register(ImmutableList<ProgramVariable> pvs, Services services) {
        for (ProgramVariable pv : pvs) {
            register(pv, services);
        }
    }


    final void register(Function f, Services services) {
        Namespace<Function> functionNames = services.getNamespaces().functions();
        if (f != null && functionNames.lookup(f.name()) == null) {
            assert f.sort() != Sort.UPDATE;
            functionNames.addSafely(f);
        }
    }

    static Term replaceQuantifiableVariables(Term term, Set<QuantifiableVariable> qvs,
            Services services) {
        Map<QuantifiableVariable, QuantifiableVariable> replaceMap = new LinkedHashMap<>();
        for (QuantifiableVariable qv : qvs) {
            replaceMap.put(qv, new LogicVariable(qv.name(), qv.sort()));
        }
        final OpReplacer op =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        term = TermLabel.removeIrrelevantLabels(term, services.getTermFactory());
        return op.replace(term);
    }

    static Set<QuantifiableVariable> collectQuantifiableVariables(Term term) {
        QuantifiableVariableVisitor qvVisitor = new QuantifiableVariableVisitor();
        term.execPreOrder(qvVisitor);
        return qvVisitor.getResult();
    }

    private static final class QuantifiableVariableVisitor implements Visitor {
        private final HashSet<QuantifiableVariable> vars = new LinkedHashSet<>();

        @Override
        public boolean visitSubtree(Term visited) {
            return true;
        }

        @Override
        public void visit(Term visited) {
            final ImmutableArray<QuantifiableVariable> boundVars = visited.boundVars();
            for (QuantifiableVariable var : boundVars) {
                vars.add(var);
            }
        }

        @Override
        public void subtreeEntered(Term subtreeRoot) { /* nothing to do */ }

        @Override
        public void subtreeLeft(Term subtreeRoot) { /* nothing to do */ }

        public Set<QuantifiableVariable> getResult() { return vars; }
    }
}
