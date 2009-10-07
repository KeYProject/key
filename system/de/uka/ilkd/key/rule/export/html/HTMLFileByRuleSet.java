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
import de.uka.ilkd.key.rule.export.RuleExportModel;
import de.uka.ilkd.key.rule.export.RuleSetModelInfo;
import de.uka.ilkd.key.rule.export.TacletModelInfo;



public class HTMLFileByRuleSet extends HTMLFile {
    
   
    public HTMLFileByRuleSet ( HTMLModel model, HTMLContainer htmlContainer ) {
        super ( model, htmlContainer, "byRuleSet.html" );
    }

    protected String getTitle () {
        return "Taclets by rule set";
    }
    
    protected String getShortTitle () {
        return "by rule set";
    }

    public void init ( RuleExportModel model ) {
        super.init(model);
        
        final Iterator<RuleSetModelInfo> it = model.ruleSets ();
        while ( it.hasNext () ){
            getFragmentAnchor ( it.next () );
        }
    }

    protected void write ( Writer w ) throws IOException {
        StringBuffer out = new StringBuffer();
        
        writeHeader(out);
        
        writeTopAnchor(out);
        
        writeNavBar(out);
        
        writeTOC(out);
        
        writeRuleSets(out);
        
        writeFooter(out);
        
        w.write(out.toString());
    }

    private void writeTOC(StringBuffer out) {
        // TOC header
        out.append ( "<!-- table of contents -->\n" );
        out.append ( "<div class=\"contents\">\n<h2>Rule sets</h2>\n" );
        if (model.getRuleSets().size () == 1) {
            out.append ( "There is 1 rule set.\n" );
        } else {
            out.append ( "There are " + model.getRuleSets().size() + " rule sets.\n" );
        }
        out.append ( "<ol>\n" );

        final Iterator<RuleSetModelInfo> it = model.ruleSets();
        while ( it.hasNext () ) {
            // TOC entry
            final RuleSetModelInfo rs = it.next ();
            final HTMLLink link = getFragmentLink ( rs );

            out.append ( "<li>" + link.toTag ( escape ( rs.name () ) ) + "</li>\n" );
        }

        // TOC footer
        out.append ( "</ol>\n</div>\n\n" );
    }
    
    private void writeRuleSets ( StringBuffer out ) {
        writeTopLink ( out );
        
        final Iterator<RuleSetModelInfo> it = model.ruleSets();
        while ( it.hasNext () ) {
            final RuleSetModelInfo rs = it.next ();

            writeRuleSetDetails ( out, rs );

            writeTopLink ( out );
        }
    }

    private void writeRuleSetDetails ( StringBuffer out, final RuleSetModelInfo rs ) {
        final HTMLAnchor anchor = getFragmentAnchor ( rs );

        // header
        out.append ( "<!-- rule set details -->\n" );
        out.append ( "<div class=\"ruleset\" id=\"" + anchor + "\">\n" );
        out.append ( "<h2>Rule set <em>" + escape ( rs.name () ) + "</em></h2>\n" );

        final ImmutableList<TacletModelInfo> localTacletList =rs.getTaclets();
        final Iterator<TacletModelInfo> it = localTacletList.iterator ();
        
        final ImmutableList<RuleSetModelInfo> intersectingSets = rs.getIntersectingSets();
        final ImmutableList<RuleSetModelInfo> superSets = rs.getSuperSets();
        final ImmutableList<RuleSetModelInfo> subSets = rs.getSubSets();
        final ImmutableList<RuleSetModelInfo> equalSets = rs.getEqualSets();
        
        if (!intersectingSets.isEmpty () || !superSets.isEmpty ()
                || !subSets.isEmpty () || !equalSets.isEmpty ()) {
            out.append ( "<dl>\n" );
            
            // definition
            if (rs.getDefinition() != null) {
            	out.append ( "<dt>definition</dt><dd>" );
            	out.append ( escape ( rs.getDefinition() ) );
            	out.append ( "</dd>\n" );
            }
            
            // intersecting sets
            if (!intersectingSets.isEmpty ()) {
                out.append ( "<dt>intersects with</dt><dd>" );
                writeRuleSetList ( out, intersectingSets );
                out.append ( "</dd>\n" );
            }
            
            // subsets
            if (!subSets.isEmpty ()) {
                out.append ( "<dt>superset of</dt><dd>" );
                writeRuleSetList ( out, subSets );
                out.append ( "</dd>\n" );
            }

            // supersets
            if (!superSets.isEmpty ()) {
                out.append ( "<dt>subset of</dt><dd>" );
                writeRuleSetList ( out, superSets );
                out.append ( "</dd>\n" );
            }

            // equal sets
            if (!equalSets.isEmpty ()) {
                out.append ( "<dt>equal to</dt><dd>" );
                writeRuleSetList ( out, equalSets );
                out.append ( "</dd>\n" );
            }
            
            out.append ( "</dl>\n" );
        }
        
        // rule list header
        if (localTacletList.size () == 1) {
            out.append ( "There is 1 rule in this rule set.\n" );
        } else {
            out.append ( "There are " + localTacletList.size ()
                    + " rules in this rule set.\n" );
        }
        out.append ( "<ol>\n" );

        // rule list elements
        while (it.hasNext ()) {
            final TacletModelInfo t = it.next ();
            out.append ( "<li>" );
            writeTacletLink ( out, t, true );
            out.append ( "</li>\n" );
        }

        // rule list footer
        out.append ( "</ol>\n" );

        // footer
        out.append ( "</div>\n\n" );
    }
    
    private void writeRuleSetList ( StringBuffer out, ImmutableList<RuleSetModelInfo> ruleSets ) {
        if (ruleSets.isEmpty ()) {
            out.append ( "none" );
        } else {
            boolean first = true;
            final Iterator<RuleSetModelInfo> it = ruleSets.iterator ();
            while (it.hasNext ()) {
                final RuleSetModelInfo ruleSet = it.next ();
                if (!first) {
                    out.append ( ", " );
                }
                writeRuleSetLink ( out, ruleSet );
                first = false;
            }
        }
    }
}
