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