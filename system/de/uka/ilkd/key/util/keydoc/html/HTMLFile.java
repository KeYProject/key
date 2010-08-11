// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.util.keydoc.html;

/** Class containing the code for the .key files HTML documentation.
 */
class HTMLFile {
    private StringBuffer htmlFile;

    /** Constructor turning a StringBuffer into a HTMLFile representation
     */
    public HTMLFile(StringBuffer htmlFile) {
	this.htmlFile= htmlFile;
    }

    public HTMLFile(String htmlFile) {
	this.htmlFile= new StringBuffer(htmlFile);
    }

    /**
       Returns the String representation of the contained HTML file.
     */
    public String getHTMLFileAsString() {
	return htmlFile.toString();
    }
}
