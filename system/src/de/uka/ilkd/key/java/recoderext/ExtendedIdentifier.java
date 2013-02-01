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

/** 
 * an extended identifier that accepts hash symbols in its name
 * but not as first character
 */
public class ExtendedIdentifier extends recoder.java.Identifier {
    /**
     * generated serialVersionUID
     */
    private static final long serialVersionUID = 1L;

    public ExtendedIdentifier(String arg0) {
        super(arg0);
    }

    public void setText(String text) {
        if (text.charAt(0)=='#') {
            throw new IllegalArgumentException
                ("No hash symbol allowed as first element in variable" +
                            "identifiers");
        } else if (text.charAt(0)=='<') {
            throw new IllegalArgumentException
            (text + " is no valid extended identifier.");
        }
        id=text.intern();
    }
    
    public ExtendedIdentifier deepClone() {
        return new ExtendedIdentifier(id);
    }
}
