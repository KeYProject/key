// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.util.keydoc.html;

import java.io.File;

/** Class containing the HTML representation of the .Key files documentation as processed by the KeyToHTMLBuilder and some other usefull information for the Director.
    It stores the three attributes fileName, shortDescription and the processed html file.
 */
class BoxedFile {
    private File file;
    private int firstLength;
    private int firstOffset;
    private HTMLFile htmlFile;

    /** Boxedfile Constructor.
     * Boxes a HTMLFile 
     * @param file the File object repressenting the .key file
     * @param firstLength
     * @param firstOffset
     * @param htmlFile The processed .key file
     */
    public BoxedFile(File file, int firstLength, int firstOffset, HTMLFile htmlFile) {
    	this.file= file;
    	this.firstLength= firstLength;
    	this.firstOffset= firstOffset;
    	this.htmlFile= htmlFile;
    }

    protected File getFile() {
    	return file;
    }

    protected int getFirstOffset() {
    	return firstOffset;
    }

    protected HTMLFile getHtmlFile() {
    	return htmlFile;
    }
    
    protected int getFirstLength() {
    	return firstLength;
    }
}
















