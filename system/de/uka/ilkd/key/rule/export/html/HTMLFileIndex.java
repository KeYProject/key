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

import java.io.IOException;
import java.io.Writer;



public class HTMLFileIndex extends HTMLFile {

    private static String bodyTemplate = getTemplate("templates/index.html");
    
    public HTMLFileIndex ( HTMLModel htmlModel, HTMLContainer htmlContainer ) {
        super ( htmlModel, htmlContainer, "index.html" );
    }

    protected String getTitle () {
        return "rule set classification";
    }

    protected String getShortTitle () {
        return "main page";
    }

    protected void write ( Writer w ) throws IOException {
        StringBuffer out = new StringBuffer();
        
        writeHeader(out);
        
        writeTopAnchor(out);
        
        writeNavBar(out);
        
        writeBody(out);
        
        writeFooter(out);
        
        w.write(out.toString());
    }
    
    private void writeBody ( StringBuffer out ) {
        String body;
        if ( bodyTemplate != null) {
            body = bodyTemplate.replaceAll("<\\?key +NAVTOP *\\?>", TOPLINK);
        } else {
            body = "template not found: index.html";
        }
        out.append ( body );
    }
}
