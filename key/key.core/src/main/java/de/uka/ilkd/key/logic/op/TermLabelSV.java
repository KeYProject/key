/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * A schema variable which matches term labels
 */
public final class TermLabelSV extends AbstractSV implements SchemaVariable, TermLabel {

    protected TermLabelSV(Name name) {
        super(name, Sort.TERMLABEL, true, false);
    }

    @Override
    public String proofToString() {
        return "\\schemaVar \\termlabel " + name() + ";\n";
    }

    @Override
    public String toString() {
        return toString("termLabel");
    }

    @Override
    public boolean validTopLevel(Term term) {
        return true;
    }

    @Override
    public Object getChild(int i) {
        throw new IndexOutOfBoundsException();
    }

    @Override
    public int getChildCount() {
        return 0;
    }
}
