// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.jmltest;

import java.io.IOException;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PresentationFeatures;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.init.SpecExtPO;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;

/**
 * The class JMLExport is used to transform given JavaDL specification to an JML
 * Specification.
 *  @author mbender@uni-koblenz.de
 * 
 */
public class JMLExport {

    final private NotationInfo notaInfo;

    final private ProgramPrinter pgr;

    final private JMLLogicPrinter lp;

    public JMLExport(SpecExtPO po, Services services) {
        notaInfo = new JMLNotationInfo();
        pgr = new ProgramPrinter();
        lp = new JMLLogicPrinter(pgr, notaInfo, services, po);
        // Used to get infix notation of some Operators
        PresentationFeatures.ENABLED = true;
        PresentationFeatures.initialize(services.getNamespaces().functions(), 
                notaInfo, null);

    }

    /**
     * Converts an JDL Term to a String in JML Syntax
     * 
     * @param t
     *                The Term in JDL to be translated into JML
     * @return a String representing a term in JML syntax
     */
    public final String translate(Term t) {

        // resets the JMLLogicPrinter
        lp.reset();
        try {

            // Try to writes current Term into the JMLLogicPrinters buffer.
            lp.printTerm(t);
        } catch (IOException e) {
            e.printStackTrace();
        }
        // Returns the string representation of the JMLLogicPrinters buffer
        return lp.result().toString();
    }

    /**
     * Converts an ArrayOf<s> into an equation in JML
     * 
     * @param pairs
     *                The ArrayOf<r> containing an Update
     * @return a String representing the Equation x == \old(y);
     */
    public final String translate(ImmutableArray<AssignmentPair> pairs) {
        if (pairs.size() > 0) {
            final StringBuffer result = new StringBuffer(translate(pairs
                    .get(0).locationAsTerm())
                    + " == \\old("
                    + translate(pairs.get(0).value())
                    + ")");
            for (int i = 1; i < pairs.size(); ++i) {
                result
                        .append(" && "
                                + translate(pairs.get(i)
                                        .locationAsTerm())
                                + " == \\old("
                                + translate(pairs.get(i)
                                        .value()) + ")");
            }
            return result.toString();
        } else {
            return "true";
        }
    }
}
