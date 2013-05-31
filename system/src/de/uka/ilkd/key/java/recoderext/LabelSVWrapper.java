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

package de.uka.ilkd.key.java.recoderext;

import recoder.java.Identifier;
import de.uka.ilkd.key.logic.op.SchemaVariable;

public class  LabelSVWrapper extends Identifier 
    implements KeYRecoderExtension, SVWrapper{

    /**
     * 
     */
    private static final long serialVersionUID = 5338442155201858492L;
    SchemaVariable sv=null;

    public LabelSVWrapper(SchemaVariable sv) {
        this.sv=sv;
    }

    protected LabelSVWrapper(LabelSVWrapper proto) {
        super(proto);
        id = proto.id;
    }

    /**
     * sets the schema variable of sort label
     * @param sv the SchemaVariable
     */
    public void setSV(SchemaVariable sv) {
	this.sv=sv;
    }

    /**
     * returns the schema variable of this label sv wrapper
     */
    public SchemaVariable getSV() {
	return sv;
    }


}
