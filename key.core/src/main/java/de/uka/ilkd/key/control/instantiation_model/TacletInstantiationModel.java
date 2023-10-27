/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.control.instantiation_model;

import java.util.ArrayList;
import java.util.Iterator;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.SortException;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

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
    /** the change event that is sent */
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
     */
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

    private void initIfChoiceModels() {
        Sequent ifseq = taclet().ifSequent();
        int asize = ifseq.antecedent().size();
        int size = asize + ifseq.succedent().size();

        if (size > 0) {
            ImmutableList<IfFormulaInstantiation> antecCand =
                IfFormulaInstSeq.createList(seq, true, services);
            ImmutableList<IfFormulaInstantiation> succCand =
                IfFormulaInstSeq.createList(seq, false, services);

            Iterator<SequentFormula> it = ifseq.iterator();
            Term ifFma;
            MatchConditions matchCond = app.matchConditions();

            ifChoiceModel = new TacletAssumesModel[size];

            for (int i = 0; i < size; i++) {
                ifFma = it.next().formula();
                ifChoiceModel[i] =
                    new TacletAssumesModel(
                        ifFma, taclet().getMatcher().matchIf((i < asize ? antecCand : succCand),
                            ifFma, matchCond, services).getFormulas(),
                        app, goal, services, nss, scm);
            }
        } else {
            ifChoiceModel = EMPTY_IF_CHOICES;
        }
    }

    private TacletApp createTacletAppFromIfs(TacletApp tacletApp) throws IfMismatchException,
            SVInstantiationParserException, MissingInstantiationException, SortMismatchException {

        ImmutableList<IfFormulaInstantiation> instList =
            ImmutableSLList.nil();

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
     *
     */
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
