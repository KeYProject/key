/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation;

import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;

import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;


public abstract class TacletVisitor implements DefaultVisitor {
    private String failureDescription = null;

    private void visit(Semisequent semiseq) {
        for (SequentFormula aSemiseq : semiseq) {
            aSemiseq.formula().execPostOrder(this);
        }
    }


    public void visit(Sequent seq) {
        visit(seq.antecedent());
        visit(seq.succedent());
    }

    public String visit(Taclet taclet, boolean visitAddrules) {
        visit(taclet.assumesSequent());
        visitFindPart(taclet);
        visitGoalTemplates(taclet, visitAddrules);
        return failureDescription;
    }

    public String visit(Taclet taclet) {
        return visit(taclet, false);
    }

    protected final void failureOccurred(String description) {
        failureDescription = description;
    }

    protected void visitFindPart(Taclet taclet) {
        if (taclet instanceof FindTaclet) {
            (((FindTaclet) taclet).find()).execPostOrder(this);
        }
    }

    protected void visitGoalTemplates(Taclet taclet, boolean visitAddrules) {
        for (var gt : taclet.goalTemplates()) {
            visit(gt.sequent());
            if (gt instanceof RewriteTacletGoalTemplate) {
                ((RewriteTacletGoalTemplate) gt).replaceWith().execPostOrder(this);
            } else {
                if (gt instanceof AntecSuccTacletGoalTemplate) {
                    visit(((AntecSuccTacletGoalTemplate) gt).replaceWith());
                }
            }
            if (visitAddrules) {
                for (var taclet1 : gt.rules()) {
                    visit((Taclet) taclet1, true);
                }
            }
        }
    }



}
