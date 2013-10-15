// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.WellDefinednessPO.Variables;

/**
 * A contract for checking the well-definedness of a jml statement. Contrary to jml
 * specifications for methods, model fields and class invariants, the well-definedness of jml
 * statements is checked "on-the-fly", i.e. before/when it is applied, since the check needs
 * the context it is placed in. Thus the technical difference to other well-definedness checks
 * is the context update and that it is not a separate contract, but another branch of the
 * specific rule of the overlying proof. The according proof sequent is built in {@link
 * #generateSequent(ProgramVariable, ProgramVariable, ProgramVariable, LocationVariable,
 *                  ProgramVariable, Term, ImmutableSet, Term, Services)}
 * Nevertheless it is imaginable to make them separate contracts.
 *
 * @author Michael Kirsten
 */
public abstract class StatementWellDefinedness extends WellDefinednessCheck {

    StatementWellDefinedness(String name, int id, IObserverFunction target,
            OriginalVariables origVars, Type type, Services services) {
        super(ContractFactory.generateContractTypeName(name, target.getContainerType(),
                                                       target, target.getContainerType()),
              id, target, origVars, type, services);
    }

    StatementWellDefinedness(String name, int id, Type type, IObserverFunction target,
                             LocationVariable heap, OriginalVariables origVars,
                             Condition requires, Term assignable, Term accessible,
                             Condition ensures, Term mby, Term rep) {
        super(name, id, type, target, heap, origVars, requires,
              assignable, accessible, ensures, mby, rep);
    }

    abstract SequentFormula generateSequent(SequentTerms seqTerms, Services services);

    public abstract SpecificationElement getStatement();

    final static ImmutableList<ProgramVariable> convertParams(ImmutableSet<ProgramVariable> set) {
        ImmutableList<ProgramVariable> list = ImmutableSLList.<ProgramVariable>nil();
        for (ProgramVariable pv: set) {
            list = list.append(pv);
        }
        return list;
    }

    @Override
    final TermAndFunc generateMbyAtPreDef(ParsableVariable self,
                                          ImmutableList<ParsableVariable> params,
                                          Services services) {
        return new TermAndFunc(TB.tt(), null);
    }

    @Override
    final ImmutableList<Term> getRest() {
        return super.getRest();
    }

    final SequentTerms createSeqTerms(POTerms po, Variables vars,
                                      Term leadingUpdate, Services services) {
        final Term pre = getPre(po.pre, vars.self, vars.heap, vars.params, false, services).term;
        final Term post = getPost(po.post, vars.result, services);
        final ImmutableList<Term> wdRest = TB.wd(po.rest, services);
        final Term updates = getUpdates(po.mod, vars.heap, vars.heap, vars.anonHeap, services);
        final Term uPost = TB.apply(updates, TB.and(TB.wd(post, services), TB.and(wdRest)));
        return new SequentTerms(leadingUpdate, pre, vars.anonHeap, po.mod, po.rest, uPost, services);
    }

    /**
     * This is where the proof sequent is built.
     * @param self The current self variable
     * @param exception The current exception variable
     * @param result The current result variable
     * @param heap The current heap
     * @param heapAtPre The current old heap
     * @param anonHeap The anonymized heap
     * @param ps The current parameter variables
     * @param leadingUpdate The context update
     * @param services The current services reference
     * @return The proof sequent for the well-definedness check
     */
    public SequentFormula generateSequent(ProgramVariable self, ProgramVariable exception,
                                          ProgramVariable result, LocationVariable heap,
                                          ProgramVariable heapAtPre, Term anonHeap,
                                          ImmutableSet<ProgramVariable> ps,
                                          Term leadingUpdate, Services services) {
        final ImmutableList<ProgramVariable> params = convertParams(ps);
        final Map<LocationVariable, ProgramVariable> atPres =
                new LinkedHashMap<LocationVariable, ProgramVariable>();
        atPres.put(heap, heapAtPre);
        final Variables vars =
                new Variables(self, result, exception, atPres, params, heap, anonHeap);
        final POTerms po = replace(this.createPOTerms(), vars);
        final Term update = replace(leadingUpdate, vars);
        final SequentTerms seqTerms = createSeqTerms(po, vars, update, services);
        return generateSequent(seqTerms, services);
    }

    public SequentFormula generateSequent(ProgramVariable self, LocationVariable heap,
                                          Term anonHeap, ImmutableSet<ProgramVariable> ps,
                                          Term leadingUpdate, Services services) {
        return generateSequent(self, null, null, heap, null, anonHeap, ps, leadingUpdate, services);
    }

    @Override
    public final String getBehaviour() {
        return "";
    }

    @Override
    public final Term getGlobalDefs() {
        return null;
    }

    @Override
    public final boolean isModel() {
        return false;
    }

    final class SequentTerms {
        final Term context;
        final Term pre;
        final Term wfAnon;
        final Term wdMod;
        final Term wdRest;
        final Term anonWdPost;

        private SequentTerms(Term context, Term pre, Term anonHeap, Term mod,
                             ImmutableList<Term> rest, Term anonWdPost, Services services) {
            this.context = context;
            this.pre = pre;
            this.wfAnon = TB.wellFormed(anonHeap, services);
            this.wdMod = TB.wd(mod, services);
            this.wdRest = TB.and(TB.wd(rest, services));
            this.anonWdPost = anonWdPost;
        }
    }
}