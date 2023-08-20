/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.statement.LabeledStatement;

/**
 * descends recursively a given program and looks for free occurrences of a specified label
 */
public class FreeLabelFinder {

    public FreeLabelFinder() {
    }

    public boolean findLabel(Label label, ProgramElement node) {
        if (!(node instanceof LabeledStatement
                && ((LabeledStatement) node).getLabel().equals(label))) {
            if (node instanceof NonTerminalProgramElement) {
                final NonTerminalProgramElement nonTerminalNode = (NonTerminalProgramElement) node;
                for (int i = 0; i < nonTerminalNode.getChildCount(); i++) {
                    if (nonTerminalNode.getChildAt(i) != null) {
                        if (findLabel(label, nonTerminalNode.getChildAt(i))) {
                            return true;
                        }
                    }
                }
            } else if (node instanceof Label) {
                return node.equals(label);
            }
        }
        return false;
    }

}
