/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.init.WellDefinednessPO.Variables;

import org.key_project.logic.op.Function;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

/**
 * A contract for checking the well-definedness of a jml statement. Contrary to jml specifications
 * for methods, model fields and class invariants, the well-definedness of jml statements is checked
 * "on-the-fly", i.e. before/when it is applied, since the check needs the context it is placed in.
 * Thus the technical difference to other well-definedness checks is the context update and that it
 * is not a separate contract, but another branch of the specific rule of the overlying proof. The
 * according proof sequent is built in
 * {@link #generateSequent}
 * Nevertheless it is imaginable to make them separate contracts.
 *
 * @author Michael Kirsten
 */
public abstract class StatementWellDefinedness extends WellDefinednessCheck {

    StatementWellDefinedness(String name, int id, IObserverFunction target,
            OriginalVariables origVars, Type type, Services services) {
        super(ContractFactory.generateContractTypeName(name, target.getContainerType(), target,
            target.getContainerType()), id, target, origVars, type, services);
    }

    StatementWellDefinedness(String name, int id, Type type, IObserverFunction target,
            LocationVariable heap, OriginalVariables origVars, Condition requires, JTerm modifiable,
            JTerm accessible, Condition ensures, JTerm mby, JTerm rep, TermBuilder tb) {
        super(name, id, type, target, heap, origVars, requires, modifiable, accessible, ensures,
            mby, rep, tb);
    }

    /**
     * This formula creates the sequent formula for the well-definedness of a jml statement in the
     * specific way, in which it is required for the specific jml statement.
     *
     * @param seqTerms
     * @param services
     * @return
     */
    abstract SequentFormula generateSequent(SequentTerms seqTerms,
            TermServices services);

    public abstract SpecificationElement getStatement();

    /**
     * Converts a set of parameter variables into a list of parameter variables
     *
     * @param set a set of parameter variables
     * @return a list of the parameter variables
     */
    final static ImmutableList<LocationVariable> convertParams(ImmutableSet<LocationVariable> set) {
        ImmutableList<LocationVariable> list = ImmutableSLList.nil();
        for (LocationVariable pv : set) {
            list = list.append(pv);
        }
        return list;
    }

    @Override
    final Function generateMbyAtPreFunc(Services services) {
        return null;
    }

    @Override
    final ImmutableList<JTerm> getRest() {
        return super.getRest();
    }

    /**
     * Aggregates and preprocesses the proof obligation data into the according terms for the
     * well-definedness sequent of the jml statement.
     *
     * @param po the proof obligation terms of the statement
     * @param vars the new (current) variables
     * @param leadingUpdate the context update of the program before the statement
     * @param localAnon anonymize local variables
     * @param services
     * @return the actual terms used in the well-definedness sequent
     */
    final SequentTerms createSeqTerms(POTerms po, Variables vars, JTerm leadingUpdate,
            JTerm localAnon, Services services) {
        final JTerm pre =
            getPre(po.pre(), vars.self, vars.heap, vars.params, services).term();
        final JTerm post = getPost(po.post(), vars.result, services);
        final ImmutableList<JTerm> wdRest = TB.wd(po.rest());
        final JTerm updates = TB.parallel(localAnon,
            getUpdates(po.modifiable(), vars.heap, vars.heap, vars.anonHeap, services));
        final JTerm uPost = TB.apply(updates, TB.and(TB.wd(post), TB.and(wdRest)));
        return new SequentTerms(leadingUpdate, pre, vars.anonHeap, po.modifiable(), po.rest(),
            uPost, services);
    }

    /**
     * This is where the proof sequent is built.
     *
     * @param self The current self variable
     * @param exception The current exception variable
     * @param result The current result variable
     * @param heap The current heap
     * @param heapAtPre The current old heap
     * @param anonHeap The anonymized heap
     * @param ps The current parameter variables
     * @param leadingUpdate The context update
     * @param localAnonUpdate anonymization update of local variables
     * @param services The current services reference
     * @return The proof sequent for the well-definedness check
     */
    public SequentFormula generateSequent(LocationVariable self,
            LocationVariable exception,
            LocationVariable result, LocationVariable heap, LocationVariable heapAtPre,
            JTerm anonHeap,
            ImmutableSet<LocationVariable> ps, JTerm leadingUpdate, JTerm localAnonUpdate,
            Services services) {
        final ImmutableList<LocationVariable> params = convertParams(ps);
        final Map<LocationVariable, LocationVariable> atPres =
            new LinkedHashMap<>();
        atPres.put(heap, heapAtPre);
        final Variables vars =
            new Variables(self, result, exception, atPres, params, heap, anonHeap);
        final POTerms po = replace(this.createPOTerms(), vars);
        final JTerm update = replace(leadingUpdate, vars);
        final JTerm localAnon = replace(localAnonUpdate, vars);
        final SequentTerms seqTerms = createSeqTerms(po, vars, update, localAnon, services);
        return generateSequent(seqTerms, services);
    }

    /**
     * This is where the proof sequent is built, however with a smaller set of variables, due to the
     * nature of the jml statement. This means no exception variable, no result variable and
     * variable for the heap of the pre-state.
     *
     * @param self self variable
     * @param heap heap variable
     * @param anonHeap anonymised heap
     * @param ps set of parameter variables
     * @param leadingUpdate the context update
     * @param localAnonUpdate anonymization update of local variables
     * @param services
     * @return The proof sequent for the well-definedness check
     */
    public SequentFormula generateSequent(LocationVariable self, LocationVariable heap,
            JTerm anonHeap, ImmutableSet<LocationVariable> ps, JTerm leadingUpdate,
            JTerm localAnonUpdate, Services services) {
        return generateSequent(self, null, null, heap, null, anonHeap, ps, leadingUpdate,
            localAnonUpdate, services);
    }

    @Override
    public abstract StatementWellDefinedness map(UnaryOperator<JTerm> op, Services services);

    @Override
    public final String getBehaviour() {
        return "";
    }

    @Override
    public final JTerm getGlobalDefs() {
        return null;
    }

    @Override
    public final JTerm getAxiom() {
        return null;
    }

    @Override
    public final boolean modelField() {
        return false;
    }

    /**
     * A data structure to pass the needed terms for the well-definedness sequent of a jml
     * statement, including the context update, pre-condition for the statement, well-formedness
     * condition for the anonymous heap, well-definedness term for the statement's
     * modifiable-clause, well-definedness term for other clauses in the statement and the
     * well-definedness term for the statement's post-condition with the according updates (heap of
     * pre-state becomes current heap and the current heap gets anonymised) applied to it.
     *
     * @author Michael Kirsten
     */
    final class SequentTerms {
        final JTerm context;
        final JTerm pre;
        final JTerm wfAnon;
        final JTerm wdModifiable;
        final JTerm wdRest;
        final JTerm anonWdPost;

        private SequentTerms(JTerm context, JTerm pre, JTerm anonHeap, JTerm modifiable,
                ImmutableList<JTerm> rest, JTerm anonWdPost, TermServices services) {
            this.context = context;
            this.pre = pre;
            this.wfAnon = anonHeap != null ? TB.wellFormed(anonHeap) : TB.tt();
            this.wdModifiable = TB.wd(modifiable);
            this.wdRest = TB.and(TB.wd(rest));
            this.anonWdPost = anonWdPost;
        }
    }
}
