// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualdebugger;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.RuleAppListener;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.proofevent.*;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;

public class UpdateLabelListener implements RuleAppListener {

    public UpdateLabelListener() {
    }

    private void analyseNodeChanges(NodeReplacement nr, int id,
            boolean looking, HashMap<PosInOccurrence, Label> labels) {
        final Iterator<NodeChange> it = nr.getNodeChanges();
        while (it.hasNext()) {
            NodeChange nc = it.next();
            if (nc instanceof NodeChangeAddFormula) {
                labels.put(((NodeChangeAddFormula) nc).getPos(), new PCLabel(
                        id, looking));
            } else if (nc instanceof NodeRedundantAddChange) {
                labels.put(((NodeRedundantAddChange) nc).getPos(), new PCLabel(
                        id, looking));
            } else if (nc instanceof NodeChangeRemoveFormula) {
                labels.remove(((NodeChangeRemoveFormula) nc).getPos());
            }

        }
    }

    private boolean containsIfTerm(Term t) {
        final OpCollector col = new OpCollector();
        t.execPreOrder(col);
        return col.contains(Op.IF_THEN_ELSE);
    }

    private boolean inUpdate(PosInOccurrence pio2) {
        PosInOccurrence pio = pio2;
        while (!pio.isTopLevel()) {
            pio = pio.up();
            if (pio.subTerm().op() instanceof QuanUpdateOperator) {
                return true;
            }
        }
        return false;
    }

    // FIXME: What is a BC Taclet and this broke because of a test of taclets
    // starting with
    // inst_ after we have renamed taclets this set of rules changed so that a
    // replacement
    // with inst is not possible! Workaround by assumption ...
    private boolean isBCTaclet(PosTacletApp tap, Node n) {

        return !(tap.taclet().name().toString().startsWith("instAll") || tap
                .taclet().name().toString().startsWith("instEx"));
    }

    // TODO duplication in prooflistner
    private boolean isLiteral(PosInOccurrence pio) {
        Term f = pio.constrainedFormula().formula();
        Operator op = f.op();
        if (this.modalityTopLevel(pio)
                && !this.containsIfTerm(pio.constrainedFormula().formula()))
            return true;
        if (op == Op.AND || op == Op.OR || op == Op.IF_THEN_ELSE
                || op == Op.IF_EX_THEN_ELSE || op == Op.EQV || op == Op.IMP
                || op == Op.AND || (op instanceof IUpdateOperator/*
                                                                     * &&
                                                                     * !containsJavaBlock(pio.constrainedFormula().formula()
                                                                     */))
            return false;
        final OpCollector col = new OpCollector();
        f.execPostOrder(col);
        return !(col.contains(Op.IF_EX_THEN_ELSE) || col
                .contains(Op.IF_THEN_ELSE));
    }

    // TODO in program mod!
    private boolean modalityTopLevel(PosInOccurrence pio) {
        Term f = pio.constrainedFormula().formula();
        if (f.arity() > 0) {
            Term sub = f.sub(f.arity() - 1);
            if (sub.op() instanceof Modality)
                return true;
        }
        return false;
    }

    public void ruleApplied(ProofEvent e) {
        RuleAppInfo info = e.getRuleAppInfo();
        setStepInfos(info);
        if (info != null) {
            Node parent = info.getOriginalNode();
            Iterator<NodeReplacement> it = info.getReplacementNodes();
            while (it.hasNext()) {
                NodeReplacement nr = it.next();
                updateLabels(parent, nr, false);
            }
        }
    }

    private HashMap<PosInOccurrence, Label> setAssumeLabel(
            HashMap<PosInOccurrence, Label> labels, Node n,
            ImmutableList<IfFormulaInstantiation> inst) {
        HashMap<PosInOccurrence, Label> l = labels;
        if (inst == null) {
            return l;
        }
        Iterator<IfFormulaInstantiation> it = inst.iterator();
        while (it.hasNext()) {
            // TODO case assume=find
            IfFormulaInstantiation next = it.next();
            if (next instanceof IfFormulaInstSeq) {
                IfFormulaInstSeq i = (IfFormulaInstSeq) next;
                PosInOccurrence pio = new PosInOccurrence(i
                        .getConstrainedFormula(), PosInTerm.TOP_LEVEL, i
                        .inAntec());

                l.put(pio, new PCLabel(-1, false));

            }
        }
        return l;
    }

    private void setStepInfos(RuleAppInfo info) {
        final Node originalNode = info.getOriginalNode();
        SourceElement actSt = // this.getActStatement(originalNode);
        VisualDebugger.getVisualDebugger().determineFirstAndActiveStatement(
                originalNode);
        final VisualDebuggerState originalNodeVDS = originalNode.getNodeInfo()
                .getVisualDebuggerState();

        int newCount = originalNodeVDS.getStatementIdcount();
        if (VisualDebugger.getVisualDebugger().isSepStatement(
                (ProgramElement) (actSt))) {
            newCount--;
        }

        final Iterator<NodeReplacement> repl = info.getReplacementNodes();
        while (repl.hasNext()) {
            NodeReplacement nr = repl.next();
            final VisualDebuggerState visualDebuggerState = nr.getNode()
                    .getNodeInfo().getVisualDebuggerState();
            visualDebuggerState.setStatementIdcount(newCount);
            visualDebuggerState.setStepOver(originalNodeVDS.getStepOver());
            visualDebuggerState.setStepOverFrom(originalNodeVDS
                    .getStepOverFrom());
        }
    }

    private void updateLabels(Node parent, NodeReplacement nr, boolean impl) {
        Node n = nr.getNode();
        int id = -1;
        boolean looking = false;

        HashMap<PosInOccurrence, Label> labels = (HashMap<PosInOccurrence, Label>) parent
                .getNodeInfo().getVisualDebuggerState().getLabels().clone();

        RuleApp app = parent.getAppliedRuleApp();

        if (app instanceof PosTacletApp) {

            final PosTacletApp tapp = (PosTacletApp) app;
            final PosInOccurrence pio = tapp.posInOccurrence().topLevel();

            if (labels.containsKey(pio) && isBCTaclet(tapp, parent)) {
                labels = setAssumeLabel(labels, n, tapp
                        .ifFormulaInstantiations());

                if (modalityTopLevel(pio) && !inUpdate(pio)) {
                    id = nr.getNode().serialNr();
                    looking = true;
                } else {
                    id = ((PCLabel) labels.get(pio)).getId();
                    looking = ((PCLabel) labels.get(pio)).isLooking();
                }
                analyseNodeChanges(nr, id, looking, labels);
            }
        } else {
            // build in rule
            if (app.posInOccurrence() != null) {
                PosInOccurrence pio = app.posInOccurrence().topLevel();
                if (labels.containsKey(pio)) {
                    id = ((PCLabel) labels.get(pio)).getId();
                    boolean isl = ((PCLabel) labels.get(pio)).isLooking();
                    analyseNodeChanges(nr, id, isl, labels);
                }

            }
        }
        updateLooking(labels);
        n.getNodeInfo().getVisualDebuggerState().setLabels(labels);
    }

    private void updateLooking(HashMap<PosInOccurrence, Label> labels) {
        boolean removelooking = true;

        for (final PosInOccurrence pio : labels.keySet()) {
            PCLabel l = (PCLabel) labels.get(pio);
            if (l.isLooking()) {
                if (!isLiteral(pio)) {
                    removelooking = false;
                }
            }
        }

        if (removelooking) {
            for (final PosInOccurrence pio : labels.keySet()) {
                PCLabel l = (PCLabel) labels.get(pio);
                l.setLooking(false);
            }
        }
    }
}
