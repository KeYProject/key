// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.control.instantiation_model;

import java.util.Iterator;

import javax.swing.DefaultComboBoxModel;

import org.antlr.runtime.RecognitionException;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.NodeOrigin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.MissingInstantiationException;
import de.uka.ilkd.key.proof.SVInstantiationParserException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.IfFormulaInstDirect;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

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
     * creates a new Termparser that parses the given string
     *
     * @param s the String to parse
     */
    private KeYParserF stringParser(String s) {
        return new KeYParserF(ParserMode.TERM, new KeYLexerF(s, ""), new Recoder2KeY(services, nss),
                services, nss, scm);
    }

    /**
     * parses and returns the term encoded as string 's'
     *
     * @param s the String to parse
     * @return the term encoded in 's'
     * @throws RecognitionException In case an exception occurs during parse.
     */
    public Term parseFormula(String s) throws RecognitionException {
        KeYParserF p = stringParser(s);
        return p.formula();
    }

    /**
     * @param pos int describes position of the if-sequent (only required for error
     *            message)
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
                        "'\\assumes'-formula: " + ProofSaver.printAnything(ifFma, services), pos,
                        -1, true);
            }

            Term term = parseFormula(manualInput);

            if (ProofIndependentSettings.DEFAULT_INSTANCE
                    .getTermLabelSettings().getUseOriginLabels()) {
                term = services.getTermBuilder().addLabelToAllSubs(term, new OriginTermLabel(
                        new NodeOrigin(
                                SpecType.INTERACTION,
                                app.rule().displayName(),
                                goal.node().serialNr())));
            }

            return new IfFormulaInstDirect(new SequentFormula(term));
        } catch (RecognitionException e) {
            throw new SVInstantiationParserException(manualInput, pos, e.charPositionInLine,
                    "Problem occured parsing a manual input" + " of an '\\assumes'-sequent.\n"
                            + e.getMessage(),
                    true).initCause(e);
        }
    }

    public boolean isManualInputSelected() {
        return getSelectedItem() == manualTextIF;
    }

}
