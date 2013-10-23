// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.SchemaVariable;

/**
 * 
 * 
 */
public class TermLabelInstantiationEntry extends InstantiationEntry {

    private final ImmutableArray<TermLabel> labels;

    TermLabelInstantiationEntry(SchemaVariable sv, ImmutableArray<TermLabel> labels) {
        super(sv);
        this.labels = labels;
    }

    /**
     * {@inheritDoc}
     */
    @Override   
    public Object getInstantiation() {
        return labels;
    }
    
    /**
     * {@inheritDoc}
     */
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(getSchemaVariable());
        sb.append(": ");
        sb.append(getInstantiation());
        sb.append('\n');
        return sb.toString();
    }

}