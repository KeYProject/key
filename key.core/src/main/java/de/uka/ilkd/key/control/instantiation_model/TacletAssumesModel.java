/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.control.instantiation_model;

import java.util.Iterator;
import javax.swing.*;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.NodeOrigin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.MissingInstantiationException;
import de.uka.ilkd.key.proof.SVInstantiationParserException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.IfFormulaInstDirect;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.util.RecognitionException;

import org.key_project.util.collection.ImmutableList;

public class TacletAssumesModel extends DefaultComboBoxModel<IfFormulaInstantiation> {

    /**
     * generated UID
     */
    private static final long serialVersionUID = -5388696072469119661L;

    private static final IfFormulaInstantiation manualTextIF = new IfFormulaInstantiation() {

        @Override
        public String toString(Services services) {
            return "Manual Input";
        }

        @Override
        public SequentFormula getConstrainedFormula() {
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

    public TacletAssumesModel(Term ifFma, ImmutableList<IfFormulaInstantiation> candidates,
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

    public static IfFormulaInstantiation[] createIfInsts(
            ImmutableList<IfFormulaInstantiation> candidates) {
        IfFormulaInstantiation[] res = new IfFormulaInstantiation[candidates.size()];
        Iterator<IfFormulaInstantiation> it = candidates.iterator();
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
    public Term parseFormula(String s) throws RecognitionException {
        return new KeyIO(services).parseExpression(s);
    }

    /**
     * @param pos int describes position of the if-sequent (only required for error message)
     * @return the selected instantiation of the if sequent
     * @throws SVInstantiationParserException
     * @throws MissingInstantiationException
     */
    public IfFormulaInstantiation getSelection(int pos)
            throws SVInstantiationParserException, MissingInstantiationException {
        if (!isManualInputSelected()) {
            return (IfFormulaInstantiation) getSelectedItem();
        }
        try {
            if (manualInput == null || "".equals(manualInput)) {
                throw new MissingInstantiationException(
                    "'\\assumes'-formula: " + ProofSaver.printAnything(ifFma, services),
                    Position.newOneBased(pos, 1),
                    true);
            }

            Term term = parseFormula(manualInput);

            if (ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings()
                    .getUseOriginLabels()) {
                term = services.getTermBuilder().addLabelToAllSubs(term,
                    new OriginTermLabel(new NodeOrigin(SpecType.USER_INTERACTION,
                        app.rule().displayName(), goal.node().serialNr())));
            }

            return new IfFormulaInstDirect(new SequentFormula(term));
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
