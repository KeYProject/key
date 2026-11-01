/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.control.instantiation_model;

import java.util.ArrayList;
import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.SortException;

import org.key_project.logic.Namespace;
import org.key_project.logic.Term;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstSeq;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.parsing.Position;

import org.jspecify.annotations.NullMarked;

@NullMarked
public class TacletInstantiationModel {

    private static final TacletAssumesModel[] EMPTY_IF_CHOICES = new TacletAssumesModel[0];

    /** the model used for the instantiation of the if-sequent */
    private TacletAssumesModel[] ifChoiceModel;
    /** the model used for the instantiation of the schemavariables */
    private final TacletFindModel tableModel;

    /**
     * the application of the Taclet of which this model is used to complete the instantiations of
     * the schemavariables and/or if-sequent
     */
    private TacletApp app;

    /** the sequent the application above is applied */
    private final Sequent seq;

    /** listeners of this model */
    private final ArrayList<ModelChangeListener> listeners = new ArrayList<>();
    /**
     * the change event that is sent
     * <p>
     * The event is wired to this model while it is still being constructed; a {@code this}-escape
     * of the standard observer/event-source pattern: the model only registers itself as the
     * event's source, and listeners observe the event once the model is fully constructed. The
     * EISOP initialization check treats the pass of {@code this} as possibly uninitialized and is
     * suppressed scoped on the field.
     */
    @SuppressWarnings({ "nullness:assignment.type.incompatible",
        "nullness:argument.type.incompatible" })
    private final ModelEvent changeEvent = new ModelEvent(this);

    /** namespace of variables */
    private final NamespaceSet nss;
    private final Services services;

    private final AbbrevMap scm;
    private final Proof proof;
    private final Goal goal;

    /**
     * Create new data model for the apply Taclet dialog wrapping a combo box model and a table
     * model.
     *
     * @param app
     * @param seq
     * @param nss
     * @param scm
     * @param goal
     *
     *        <p>
     *        The {@link #initIfChoiceModels()} call operates on {@code this} while the receiver is
     *        still under initialization (EISOP initialization check); safe here since it only
     *        builds the choice-model cache from the already-assigned fields above. The
     *        {@code ifChoiceModel} field is (re)built lazily by that same helper, which the
     *        initialization check cannot verify either; both differences are suppressed with
     *        scoped keys.
     */
    @SuppressWarnings({ "nullness:method.invocation.invalid",
        "nullness:initialization.fields.uninitialized" })
    public TacletInstantiationModel(TacletApp app, Sequent seq, NamespaceSet nss, AbbrevMap scm,
            Goal goal) {
        this.app = app;
        this.seq = seq;
        this.proof = goal.proof();
        this.services = proof.getServices();
        this.nss = nss;
        this.scm = scm;
        this.goal = goal;
        initIfChoiceModels();

        tableModel = new TacletFindModel(app, services, nss, scm, goal);
    }

    public void addModelChangeListener(ModelChangeListener l) {
        listeners.add(l);
    }

    public void removeModelChangeListener(ModelChangeListener l) {
        listeners.remove(l);
    }

    public TacletAssumesModel ifChoiceModel(int i) {
        return ifChoiceModel[i];
    }

    public int ifChoiceModelCount() {
        return ifChoiceModel.length;
    }

    public TacletFindModel tableModel() {
        return tableModel;
    }

    public TacletApp application() {
        return app;
    }

    public Taclet taclet() {
        return app.taclet();
    }

    public TacletApp tacletApp() {
        return app;
    }

    public Proof proof() {
        return proof;
    }

    public Term ifFma(int i) {
        return ifChoiceModel(i).ifFma();
    }

    /**
     * Initializes the per-formula choice models of this instantiation model.
     * <p>
     * The matcher of the underlying taclet is present for a closed model; the dereference of the
     * (nullable) matcher is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    private void initIfChoiceModels() {
        Sequent ifseq = taclet().assumesSequent();
        int asize = ifseq.antecedent().size();
        int size = asize + ifseq.succedent().size();

        if (size > 0) {
            ImmutableArray<AssumesFormulaInstantiation> antecCand =
                AssumesFormulaInstSeq.createList(seq, true, services);
            ImmutableArray<AssumesFormulaInstantiation> succCand =
                AssumesFormulaInstSeq.createList(seq, false, services);

            Iterator<SequentFormula> it = ifseq.iterator();
            JTerm ifFma;
            MatchConditions matchCond = app.matchConditions();

            ifChoiceModel = new TacletAssumesModel[size];

            for (int i = 0; i < size; i++) {
                ifFma = (JTerm) it.next().formula();
                ifChoiceModel[i] =
                    new TacletAssumesModel(
                        ifFma,
                        taclet().getMatcher().matchAssumes((i < asize ? antecCand : succCand),
                            ifFma, matchCond, services).candidates(),
                        app, goal, services, nss, scm);
            }
        } else {
            ifChoiceModel = EMPTY_IF_CHOICES;
        }
    }

    /**
     * Builds the taclet application from the if-side formulas chosen in the dialog, or throws a
     * mismatch exception when the assumptions cannot be instantiated.
     * <p>
     * The application is re-assigned from {@code setIfFormulaInstantiations}, which reports an
     * unresolvable instantiation with {@code null}; the code immediately follows up with an
     * explicit {@code null} check that raises {@link IfMismatchException}, so the transitory
     * {@code null} never reaches a non-null position. The re-assignment and the {@code null}
     * {@code givenSort} of the sort-mismatch report are suppressed scoped on this method.
     */
    @SuppressWarnings("nullness:assignment.type.incompatible")
    private TacletApp createTacletAppFromIfs(TacletApp tacletApp) throws IfMismatchException,
            SVInstantiationParserException, MissingInstantiationException, SortMismatchException {

        ImmutableList<AssumesFormulaInstantiation> instList =
            ImmutableList.nil();

        for (int i = ifChoiceModel.length - 1; i >= 0; --i) {
            instList = instList.prepend(ifChoiceModel[i].getSelection(i));
        }

        try {
            tacletApp = tacletApp.setIfFormulaInstantiations(instList, services);
        } catch (SortException e) {
            throw new SortMismatchException("'\\assumes'-sequent", null, Position.UNDEFINED);
        }

        if (tacletApp == null) {
            throw new IfMismatchException(
                "Mismatch of '\\assumes'-formulas.\n" + "Reasons may be: ambigous instantiation "
                    + "of schemavariables or unsatisfiable constraints.");
        }

        return tacletApp;
    }

    public String getStatusString() {
        TacletApp rapp = app;

        if (rapp == null) {
            return "Rule is not applicable.";
        }

        try {
            rapp = createTacletApp();
        } catch (Exception e) {
            return "Rule is not applicable.\n Detail:" + e.getMessage();
        }

        if (rapp.complete()) {
            return "Instantiation is OK.";
        } else {
            return "Instantiations are incomplete.";
        }

    }

    public TacletApp createTacletApp() throws SVInstantiationException {
        return createTacletAppFromIfs(tableModel.createTacletAppFromVarInsts());
    }

    private void informListenerAboutModelChange() {
        for (ModelChangeListener listener : listeners) {
            if (listener != null) {
                listener.modelChanged(changeEvent);
            }
        }
    }

    /** sets the manual if-input */
    public void setManualInput(int i, String s) {
        ifChoiceModel(i).setInput(s);
        informListenerAboutModelChange();
    }

    /**
     * replaces the TacletApp of this ApplyTacletDialogModel by an TacletApp where all name
     * conflicts are resolved and thus the parser is enabled to accept variables from the context or
     * the prefix of the Taclet.
     * <p>
     * Conflict resolution fails with a {@code null} result only when a variable name clash cannot
     * be resolved; the field then holds that unresolved app, which the invoking dialog reports to
     * the user rather than dereferencing. Assigning the (nullable-typed) resolution result to the
     * non-null field is suppressed scoped on this method, preserving the pre-analysis behavior.
     */
    @SuppressWarnings("nullness:assignment.type.incompatible")
    public void prepareUnmatchedInstantiation() {
        app = app.prepareUserInstantiation(services);
    }

    public Namespace<IProgramVariable> programVariables() {
        return nss.programVariables();
    }

    /**
     * Gets the services in use by this object.
     *
     * @return this model's Services
     */
    public Services getServices() {
        return services;
    }

}
