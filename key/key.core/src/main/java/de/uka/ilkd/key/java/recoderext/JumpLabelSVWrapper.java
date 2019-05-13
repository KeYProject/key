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

package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.SchemaVariable;

public class JumpLabelSVWrapper implements SVWrapper {

    private SchemaVariable label; 
    
    public JumpLabelSVWrapper(SchemaVariable l) {
        label = l;
    }
    
    public SchemaVariable getSV() {        
        return label;
    }

    public void setSV(SchemaVariable sv) {
        label = sv;        
    }
    
    public String toString() {
        return ""+label;
    }

}