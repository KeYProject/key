// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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
import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.rule.export.RuleExportModel;
import de.uka.ilkd.key.rule.export.TacletModelInfo;



public class HTMLFileByRuleName extends HTMLFile {
    public static final int TACLETS_PER_FILE = 10;

    public HTMLFileByRuleName(HTMLModel model, HTMLContainer htmlContainer) {
        super(model, htmlContainer, "byRuleName.html");
    }
    
    protected String getTitle () {
        return "Taclets by rule name";
    }
    
    protected String getShortTitle () {
        return "by rule name";
    }

    public void write(Writer w) throws IOException {
        StringBuffer out = new StringBuffer();
        
        writeHeader(out);
        
        writeTopAnchor(out);
        
        writeNavBar(out);
        
        writeTOC(out);
        
        writeFooter(out);
        
        w.write(out.toString());
        
        writeAllFiles();
    }
    
    public void init(RuleExportModel model) {
        super.init(model);
        
        final Iterator<TacletModelInfo> it = model.taclets();
        int n = 0;
        ImmutableList<TacletModelInfo> list = ImmutableSLList.<TacletModelInfo>nil();
        while ( it.hasNext () ) {
            final TacletModelInfo t = it.next ();
            list = list.append( t );
            n++;
            if ( n % TACLETS_PER_FILE == 0 ) {
                HTMLFile file = new HTMLFileTaclet(htmlModel(), this, list, n / TACLETS_PER_FILE);
                list = ImmutableSLList.<TacletModelInfo>nil();
            }
        }
        if ( !list.isEmpty() ) {
            HTMLFile file = new HTMLFileTaclet(htmlModel(), this, list, n / TACLETS_PER_FILE + 1);
        }
        
        initAllFiles( model );
    }
    
    private void writeTOC(StringBuffer out) {
        // TOC header
        out.append ( "<!-- table of contents -->\n" );
        out.append ( "<div class=\"contents\">\n<h2>Rules</h2>\n" );
        if (model.getTaclets().size() == 1) {
            out.append ( "There is 1 rule.\n" );
        } else {
            out.append ( "There are " + model.getTaclets().size() + " rules.\n" );
        }
        out.append ( "<ol>\n" );
        
        final Iterator<TacletModelInfo> it = model.taclets();
        while ( it.hasNext () ) {
            // TOC entry
            final TacletModelInfo t = it.next ();
            
            out.append( "<li>" );
            writeTacletLink ( out, t, true );
            out.append("</li>\n");
        }
        
        // TOC footer
        out.append ( "</ol>\n</div>\n\n" );

        writeTopLink ( out );
    }
    
}
