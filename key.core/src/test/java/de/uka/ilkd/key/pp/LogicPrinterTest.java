/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import java.io.IOException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class LogicPrinterTest {

    /**
     * Tests that no stackoverflow exception is thrown when pretty printing a taclet
     * containing a modality.
     */
    @Test
    void printModalityTerm() {
        NamespaceSet nss = new NamespaceSet();
        Services services = TacletForTests.services();// new
                                                      // Services(AbstractProfile.getDefaultProfile());
        KeyIO io = new KeyIO(services, services.getNamespaces());
        FindTaclet taclet = null;
        try {
            taclet = (FindTaclet) io
                    .load(
                        """
                                \\rules { test {
                                   \\schemaVar \\modalOperator {diamond, box, diamond_transaction, box_transaction} #allmodal;
                                   \\find(\\modality{#allmodal} {}\\endmodality(true))
                                   \\replacewith(\\modality{#allmodal} {}\\endmodality(true))
                                };}
                                """)
                    .loadComplete().get(0);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        LogicPrinter lp = LogicPrinter.purePrinter(new NotationInfo(), services);
        lp.printTaclet(taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS, true, false);
        SVInstantiations inst = SVInstantiations.EMPTY_SVINSTANTIATIONS.add(
            ((Modality) taclet.find().op()).kind(),
            Modality.JavaModalityKind.DIA, services);
        lp.printTaclet(taclet, inst, true, false);
        assertTrue(true);
    }
}
