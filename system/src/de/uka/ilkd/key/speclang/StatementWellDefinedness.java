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
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
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

    /**
     * This formula creates the sequent formula for the well-definedness of a jml statement
     * in the specific way, in which it is required for the specific jml statement.
     * @param seqTerms
     * @param services
     * @return
     */
    abstract SequentFormula generateSequent(SequentTerms seqTerms, Services services);

    public abstract SpecificationElement getStatement();

    /**
     * Converts a set of parameter variables into a list of parameter variables
     * @param set a set of parameter variables
     * @return a list of the parameter variables
     */
    final static ImmutableList<ProgramVariable> convertParams(ImmutableSet<ProgramVariable> set) {
        ImmutableList<ProgramVariable> list = ImmutableSLList.<ProgramVariable>nil();
        for (ProgramVariable pv: set) {
            list = list.append(pv);
        }
        return list;
    }

    @Override
    final Function generateMbyAtPreFunc(Services services) {
        return null;
    }

    @Override
    final ImmutableList<Term> getRest() {
        return super.getRest();
    }

    /**
     * Aggregates and preprocesses the proof obligation data into the according terms for the
     * well-definedness sequent of the jml statement.
     * @param po the proof obligation terms of the statement
     * @param vars the new (current) variables
     * @param leadingUpdate the context update of the program before the statement
     * @param services
     * @return the actual terms used in the well-definedness sequent
     */
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

    /**
     * This is where the proof sequent is built, however with a smaller set of variables,
     * due to the nature of the jml statement. This means no exception variable, no result
     * variable and variable for the heap of the pre-state.
     * @param self self variable
     * @param heap heap variable
     * @param anonHeap anonymised heap
     * @param ps set of parameter variables
     * @param leadingUpdate the context update
     * @param services
     * @return The proof seuqne t for the well-definedness check
     */
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
    public final Term getAxiom() {
        return null;
    }

    @Override
    public final boolean modelField() {
        return false;
    }

    /**
     * A data structure to pass the needed terms for the well-definedness sequent of a jml
     * statement, including the context update, pre-condition for the statement, well-formedness
     * condition for the anonymous heap, well-definedness term for the statement's assignable-clause,
     * well-definedness term for other clauses in the statement and the well-definedness term for
     * the statement's post-condition with the according updates (heap of pre-state becomes current
     * heap and the current heap gets anonymised) applied to it.
     *
     * @author Michael Kirsten
     */
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
            this.wfAnon = anonHeap != null ? TB.wellFormed(anonHeap, services) : TB.tt();
            this.wdMod = TB.wd(mod, services);
            this.wdRest = TB.and(TB.wd(rest, services));
            this.anonWdPost = anonWdPost;
        }
    }
}