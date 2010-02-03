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



public class HTMLFragmentLink extends HTMLLink {
    private HTMLFile sourceFile;
    private HTMLFragment targetFragment;
    
    public HTMLFragmentLink ( HTMLFile sourceFile, HTMLFragment targetFragment ) {
        this.sourceFile = sourceFile;
        this.targetFragment = targetFragment;
    }
    
    public String toString () {
        return getURL ();
    }
    
    protected String getURL () {
        StringBuffer rv = new StringBuffer();
        final HTMLFile targetFile = targetFragment.getFile(); 
        if (targetFile != null) {
            if (sourceFile != targetFile) {
                rv.append(sourceFile.getRelPath(targetFile));
            }
            
            final String id = targetFragment.getId();
            if (id != null) {
                rv.append("#");
                rv.append(id);
            }
        }
        return rv.toString();
    }
    /**
     * @return Returns the sourceFile.
     */
    HTMLFile getSourceFile () {
        return sourceFile;
    }
    
    /**
     * @param sourceFile The sourceFile to set.
     */
    void setSourceFile ( HTMLFile sourceFile ) {
        this.sourceFile = sourceFile;
    }
    
    
    /**
     * @return Returns the targetFragment.
     */
    Object getTargetFragment () {
        return targetFragment;
    }
    
    /**
     * @param targetFragment The targetFragment to set.
     */
    void setTargetFragment ( HTMLFragment targetFragment ) {
        this.targetFragment = targetFragment;
    }

}
