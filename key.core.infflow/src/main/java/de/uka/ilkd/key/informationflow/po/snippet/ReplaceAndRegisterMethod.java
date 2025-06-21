/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import java.util.*;

import de.uka.ilkd.key.informationflow.proof.init.StateVars;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.LinkedHashMap;

import org.key_project.logic.Namespace;
import org.key_project.logic.Visitor;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;


/**
 * Generate term "self != null".
 * <p/>
 *
 * @author christoph
 */
abstract class ReplaceAndRegisterMethod {

    final JTerm replace(JTerm term, ProofObligationVars origVars, ProofObligationVars poVars,
            TermBuilder tb) {
        JTerm intermediateResult = replace(term, origVars.pre, poVars.pre, tb);
        return replace(intermediateResult, origVars.post, poVars.post, tb);
    }


    final JTerm replace(JTerm term, StateVars origVars, StateVars poVars, TermBuilder tb) {
        LinkedHashMap<JTerm, JTerm> map = new LinkedHashMap<>();

        Iterator<JTerm> origVarsIt;
        Iterator<JTerm> poVarsIt;
        assert origVars.paddedTermList.size() == poVars.paddedTermList.size();
        origVarsIt = origVars.paddedTermList.iterator();
        poVarsIt = poVars.paddedTermList.iterator();
        while (origVarsIt.hasNext()) {
            JTerm origTerm = origVarsIt.next();
            JTerm poTerm = poVarsIt.next();
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


    final JTerm[] replace(JTerm[] terms, StateVars origVars, StateVars poVars, TermBuilder tb) {
        final JTerm[] result = new JTerm[terms.length];
        for (int i = 0; i < terms.length; i++) {
            result[i] = replace(terms[i], origVars, poVars, tb);

        }
        return result;
    }


    final InfFlowSpec replace(InfFlowSpec terms, StateVars origVars, StateVars poVars,
            TermBuilder tb) {
        ImmutableList<JTerm> resultPreExps = ImmutableSLList.nil();
        for (JTerm t : terms.preExpressions) {
            resultPreExps = resultPreExps.append(replace(t, origVars, poVars, tb));
        }
        ImmutableList<JTerm> resultPostExps = ImmutableSLList.nil();
        for (JTerm t : terms.postExpressions) {
            resultPostExps = resultPostExps.append(replace(t, origVars, poVars, tb));
        }
        ImmutableList<JTerm> resultNewObjecs = ImmutableSLList.nil();
        for (JTerm t : terms.newObjects) {
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


    final JTerm replace(JTerm term, JTerm[] origVars, JTerm[] poVars, TermBuilder tb) {
        LinkedHashMap<JTerm, JTerm> map = new LinkedHashMap<>();

        assert origVars.length == poVars.length;
        for (int i = 0; i < origVars.length; i++) {
            JTerm origTerm = origVars[i];
            JTerm poTerm = poVars[i];
            if (origTerm != null && poTerm != null) {
                assert origTerm.sort().equals(poTerm.sort());
                map.put(origTerm, poTerm);
            }
        }

        OpReplacer or = new OpReplacer(map, tb.tf());

        return or.replace(term);
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
            assert f.sort() != JavaDLTheory.UPDATE;
            functionNames.addSafely(f);
        }
    }

    static JTerm replaceQuantifiableVariables(JTerm term, Set<QuantifiableVariable> qvs,
            Services services) {
        Map<QuantifiableVariable, QuantifiableVariable> replaceMap = new LinkedHashMap<>();
        for (QuantifiableVariable qv : qvs) {
            replaceMap.put(qv, new LogicVariable(qv.name(), qv.sort()));
        }
        final OpReplacer op =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        term = TermLabelManager.removeIrrelevantLabels(term, services.getTermFactory());
        return op.replace(term);
    }

    static Set<QuantifiableVariable> collectQuantifiableVariables(JTerm term) {
        QuantifiableVariableVisitor qvVisitor = new QuantifiableVariableVisitor();
        term.execPreOrder(qvVisitor);
        return qvVisitor.getResult();
    }

    private static final class QuantifiableVariableVisitor implements Visitor<JTerm> {
        private final HashSet<QuantifiableVariable> vars = new LinkedHashSet<>();

        @Override
        public boolean visitSubtree(JTerm visited) {
            return true;
        }

        @Override
        public void visit(JTerm visited) {
            for (var boundVar : visited.boundVars()) {
                vars.add(boundVar);
            }
        }

        @Override
        public void subtreeEntered(JTerm subtreeRoot) { /* nothing to do */ }

        @Override
        public void subtreeLeft(JTerm subtreeRoot) { /* nothing to do */ }

        public Set<QuantifiableVariable> getResult() { return vars; }
    }
}
