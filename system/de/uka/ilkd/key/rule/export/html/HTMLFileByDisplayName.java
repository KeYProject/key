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

import de.uka.ilkd.key.rule.export.*;



public class HTMLFileByDisplayName extends HTMLFile {
    public HTMLFileByDisplayName ( HTMLModel htmlModel, HTMLContainer htmlContainer ) {
        super ( htmlModel, htmlContainer, "byDisplayName.html" );
    }

    protected String getTitle () {
        return "Taclets by display name";
    }

    protected String getShortTitle () {
        return "by display name";
    }

    protected void init ( RuleExportModel model ) {
        super.init(model);
        
        final IteratorOfDisplayNameModelInfo it = model.displayNames();
        while ( it.hasNext () ) {
            final DisplayNameModelInfo dn = it.next ();
            getFragmentAnchor(dn);
        }
    }

    protected void write ( Writer w ) throws IOException {
        final StringBuffer out = new StringBuffer();
        
        writeHeader(out);
        writeTopAnchor(out);
        writeNavBar(out);
        writeTOC(out);
        writeDisplayNames(out);
        writeFooter(out);
        
        w.write(out.toString());
    }

    private void writeTOC(StringBuffer out) {
        // TOC header
        out.append ( "<!-- table of contents -->\n" );
        out.append ( "<div class=\"contents\">\n<h2>Display names</h2>\n" );
        if (model.getDisplayNames ().size () == 1) {
            out.append ( "There is 1 unique display name.\n" );
        } else {
            out.append ( "There are " + model.getDisplayNames ().size ()
                    + " unique display names.\n" );
        }
        out.append ( "<ol>\n" );

        final IteratorOfDisplayNameModelInfo it = model.displayNames();
        while ( it.hasNext () ) {
            // TOC entry
            final DisplayNameModelInfo dn = it.next ();
            
            final ListOfTacletModelInfo taclets = dn.getTaclets();
            int tacletCount = taclets.size();

            out.append ( "<li>" );
            writeDisplayNameLink ( out, dn );
            if ( tacletCount > 1 ) {
                out.append ( " (" + tacletCount + " rules" );
                String differences = getDifferences ( taclets );
                if ( !"".equals ( differences ) ) {
                    out.append ( differences );
                }
                out.append ( ")" );
            }
            out.append ( "</li>\n" );
        }

        // TOC footer
        out.append ( "</ol>\n</div>\n\n" );
    }
    
    private String getDifferences ( ListOfTacletModelInfo taclets ) {
        TacletModelInfo t0 = taclets.head ();
        final IteratorOfTacletModelInfo it = taclets.tail ().iterator ();
        boolean differentOptions = false;
        boolean differentIntroducer = false;
        while (it.hasNext ()) {
            final TacletModelInfo t = it.next ();
            if (!t0.name ().equals ( t.name () )) {
                return "";
            }
            if ( t0.getIntroducingTaclet() != t.getIntroducingTaclet() ) {
                differentIntroducer = true;
            } else {
                // assume different options
                differentOptions = true;
            }
        }
        String rv = "";
        if ( differentIntroducer ) {
            rv = rv + ", different introducer";
        }
        if ( differentOptions ) {
            rv = rv + ", different options";
        }
        return rv;
    }

    private void writeDisplayNames(StringBuffer out) {
        writeTopLink(out);
        final IteratorOfDisplayNameModelInfo it = model.displayNames();
        while ( it.hasNext () ) {
            final DisplayNameModelInfo dn = it.next ();
            
            writeDisplayNameDetails ( out, dn );

            writeTopLink(out);
        }
    }

    private void writeDisplayNameDetails ( StringBuffer out, final DisplayNameModelInfo dn ) {
        final HTMLAnchor anchor = getFragmentAnchor ( dn );
        
        // header
        out.append ( "<!-- display name details -->\n" );
        out.append ( "<div class=\"displayname\" id=\"" + anchor + "\">\n" );
        out.append ( "<h2>" + dn + "</h2>\n" );
        
        final ListOfTacletModelInfo taclets = dn.getTaclets();
        if ( taclets.size () == 1 ) {
            out.append ( "There is 1 taclet with this display name.\n" );
        } else {
            out.append ( "There are " + taclets.size ()
                    + " taclets with this display name.\n" );
        }
        out.append ( "<ol>\n" );
        
        final IteratorOfTacletModelInfo it = taclets.iterator ();
        while ( it.hasNext () ) {
            final TacletModelInfo t = it.next ();
            
            out.append( "<li>" );
            writeTacletLink ( out, t, true );
            out.append("</li>\n");
        }
        
        out.append ( "</ol>\n" );
        
        // footer
        out.append ( "</div>\n" );
    }
}
