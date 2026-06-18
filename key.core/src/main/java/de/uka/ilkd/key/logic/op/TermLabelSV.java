/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.label.TermLabel;

import org.key_project.logic.Name;

/**
 * A schema variable which matches term labels
 */
public final class TermLabelSV extends JOperatorSV implements TermLabel {

    TermLabelSV(Name name) {
        super(name, JavaDLTheory.TERMLABEL, true, false);
    }

    @Override
    public String toString() {
        return toString("termLabel");
    }

    @Override
    public int getTLChildCount() {
        return 0;
    }

    @Override
    public Object getTLChild(int i) {
        throw new IndexOutOfBoundsException();
    }
}
