/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.control.instantiation_model;

import java.util.Iterator;
import javax.swing.*;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.label.OriginTermLabel.NodeOrigin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.MissingInstantiationException;
import de.uka.ilkd.key.proof.SVInstantiationParserException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.RecognitionException;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstDirect;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

public class TacletAssumesModel extends DefaultComboBoxModel<AssumesFormulaInstantiation> {

    /**
     * generated UID
     */
    private static final long serialVersionUID = -5388696072469119661L;

    private static final AssumesFormulaInstantiation manualTextIF =
        new AssumesFormulaInstantiation() {

            @Override
            public String toString(LogicServices services) {
                return "Manual Input";
            }

            @Override
            public SequentFormula getSequentFormula() {
                return null;
            }
        };

    private String manualInput;
    private final Term ifFma;

    private final NamespaceSet nss;
    private final AbbrevMap scm;
    private final Services services;
    private final TacletApp app;
    private final Goal goal;

    public TacletAssumesModel(Term ifFma, ImmutableList<AssumesFormulaInstantiation> candidates,
            TacletApp app, Goal goal, Services services, NamespaceSet nss, AbbrevMap scm) {
        super(createIfInsts(candidates));

        this.ifFma = ifFma;
        this.services = services;
        this.nss = nss;
        this.scm = scm;
        this.app = app;
        this.goal = goal;

        addElement(manualTextIF);
        manualInput = "";
    }

    public void setInput(String s) {
        manualInput = s;
    }

    public Term ifFma() {
        return ifFma;
    }

    public static AssumesFormulaInstantiation[] createIfInsts(
            ImmutableList<AssumesFormulaInstantiation> candidates) {
        AssumesFormulaInstantiation[] res = new AssumesFormulaInstantiation[candidates.size()];
        Iterator<AssumesFormulaInstantiation> it = candidates.iterator();
        int i = 0;

        while (it.hasNext()) {
            res[i] = it.next();
            ++i;
        }

        return res;
    }

    /**
     * parses and returns the term encoded as string 's'
     *
     * @param s the String to parse
     * @return the term encoded in 's'
     * @throws RecognitionException In case an exception occurs during parse.
     */
    public JTerm parseFormula(String s) throws RecognitionException {
        return new KeyIO(services).parseExpression(s);
    }

    /**
     * @param pos int describes position of the if-sequent (only required for error message)
     * @return the selected instantiation of the if sequent
     * @throws SVInstantiationParserException
     * @throws MissingInstantiationException
     */
    public AssumesFormulaInstantiation getSelection(int pos)
            throws SVInstantiationParserException, MissingInstantiationException {
        if (!isManualInputSelected()) {
            return (AssumesFormulaInstantiation) getSelectedItem();
        }
        try {
            if (manualInput == null || manualInput.isEmpty()) {
                throw new MissingInstantiationException(
                    "'\\assumes'-formula: " + ProofSaver.printAnything(ifFma, services),
                    Position.newOneBased(pos, 1),
                    true);
            }

            JTerm term = parseFormula(manualInput);
            term = services.getTermBuilder().addLabelToAllSubs(term,
                new NodeOrigin(SpecType.USER_INTERACTION,
                    app.rule().displayName(), goal.node().serialNr()));

            return new AssumesFormulaInstDirect(new SequentFormula(term));
        } catch (RecognitionException e) {
            throw new SVInstantiationParserException(manualInput,
                Position.fromOneZeroBased(pos, e.charPositionInLine),
                "Problem occured parsing a manual input" + " of an '\\assumes'-sequent.\n"
                    + e.getMessage(),
                true).initCause(e);
        }
    }

    public boolean isManualInputSelected() {
        return getSelectedItem() == manualTextIF;
    }

}
