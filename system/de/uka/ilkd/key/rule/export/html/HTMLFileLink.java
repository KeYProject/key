// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//This file is part of KeY - Integrated Deductive Software Design 
//Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                      and Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License.
//See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.export.html;



public class HTMLFileLink extends HTMLLink {
    private HTMLFile sourceFile;
    private HTMLFile targetFile;
    
    public HTMLFileLink ( HTMLFile sourceFile, HTMLFile targetFile ) {
        this.sourceFile = sourceFile;
        this.targetFile = targetFile;
    }
    
    public String toString () {
        return getURL ();
    }
    
    protected String getURL () {
        return sourceFile.getRelPath ( targetFile );
    }
}
