// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
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
import java.util.Arrays;
import java.util.Comparator;

import de.uka.ilkd.key.rule.export.*;



public class HTMLFileByOption extends HTMLFile {
    
    private OptionModelInfo[][] options;
    private ListOfCategoryModelInfo categories;
    private int numCombinations;
    private int[] strides;
    private int[] numActives;

    public HTMLFileByOption ( HTMLModel htmlModel, HTMLContainer htmlContainer ) {
        super ( htmlModel, htmlContainer, "byOption.html" );
    }

    protected String getTitle () {
        return "Taclets by option";
    }

    protected String getShortTitle () {
        return "by option";
    }

    public void init ( RuleExportModel model ) {
        super.init(model);
        
        final IteratorOfOptionModelInfo it = model.options ();
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
        
        writeChoiceTable(out);
        
        writeOptions(out);
        
        writeFooter(out);
        
        w.write(out.toString());
    }

    private void writeTOC(StringBuffer out) {
        // TOC header
        out.append ( "<!-- table of contents -->\n" );
        out.append ( "<div class=\"contents\">\n<h2>Options</h2>\n" );
        int numChoices = model.getOptions().size ();
        if ( numChoices == 1 ) {
            out.append ( "There is 1 option" );
        } else {
            out.append ( "There are " + numChoices + " options" );
        }
        int numCategories = model.getCategories().size();
        if ( numCategories == 1 ) {
            out.append ( " in 1 category.\n" );
        } else {
            out.append ( " in " + numCategories + " categories.\n" );
        }
        
        out.append ( "<ul>\n" );
        
        final IteratorOfCategoryModelInfo it = model.categories();
        while ( it.hasNext () ) {
            final CategoryModelInfo cat = it.next ();
            out.append ( "<li>" + cat + "\n" );
            out.append ( "<ol>\n" );
            
            final IteratorOfOptionModelInfo it2 = cat.getOptions().iterator();
            while ( it2.hasNext () ) {
                final OptionModelInfo opt = it2.next ();
                final HTMLLink link = getFragmentLink ( opt );
                out.append ( "<li>" + link.toTag ( opt.name () ) + "</li>\n" );
            }
            
            out.append ( "</ol>\n" );
            out.append ( "</li>\n" );
        }
        
        // TOC footer
        out.append ( "</ul>\n</div>\n\n" );
    }
    
    private void writeOptions ( StringBuffer out ) {
        writeTopLink ( out );
        
        final IteratorOfOptionModelInfo it = model.options();
        while ( it.hasNext () ) {
            final OptionModelInfo opt = it.next ();

            writeOptionDetails ( out, opt );

            writeTopLink ( out );
        }
    }
    
    private void writeOptionDetails ( StringBuffer out, OptionModelInfo opt ) {
        final HTMLAnchor anchor = getFragmentAnchor ( opt );
        
        // header
        out.append ( "<!-- option details -->\n" );
        out.append ( "<div class=\"option\" id=\"" + anchor + "\">\n" );
        out.append ( "<h2>" + opt.name() + "</h2>\n" );
        
        final ListOfTacletModelInfo taclets = opt.getTaclets();
        if ( taclets.size () == 1 ) {
            out.append ( "There is 1 taclet belonging to this option.\n" );
        } else {
            out.append ( "There are " + taclets.size ()
                    + " taclets belonging to this option.\n" );
        }
        
        out.append ( "<dl>\n" );
        
        // alternative choices
        ListOfOptionModelInfo alternatives = opt.getCategory().getOptions().removeAll(opt);
        out.append ( "<dt>alternatives</dt><dd>" );
        if ( alternatives.size() == 0) {
            out.append ( "none" );
        } else {
            writeOptionList ( out, alternatives );
        }
        out.append ( "</dd>\n" );
        
        out.append ( "</dl>\n" );
        
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
    
    private ListOfCategoryModelInfo sortCategoriesByChoices ( ListOfCategoryModelInfo cats ) {
        CategoryModelInfo[] catArray = cats.toArray();
        Arrays.sort(catArray, new Comparator () {
           public int compare ( Object a, Object b ) {
               return ((CategoryModelInfo) a).getOptions().size()
                        - ((CategoryModelInfo) b).getOptions().size();
           }
        });
        return SLListOfCategoryModelInfo.EMPTY_LIST.prepend(catArray);
    }
   
    private void writeChoiceTable (StringBuffer out) {
        categories = sortCategoriesByChoices(model.getCategories());
        final int numCategories = categories.size();
        options = new OptionModelInfo[numCategories][];
        int[] numChoices = new int[numCategories];
        numCombinations = 1;
        int n = 0;
        out.append ( "<table border=\"1\">\n" );
        out.append ( "<caption>Number of active taclets</caption>\n" );
        out.append ( "<thead>\n<tr>\n" );
        final IteratorOfCategoryModelInfo it = categories.iterator();
        while ( it.hasNext () ) {
            final CategoryModelInfo cat = it.next ();
            options[n] = cat.getOptions().toArray();
            numChoices[n] = options[n].length;
            numCombinations *= numChoices[n];
            out.append ( "<td>" + cat.name() + "</td>" );
            n++;
        }
        
        strides = new int[numCategories];
        int stride = 1;
        for ( n = numCategories-1; n >= 0; n-- ) {
            strides[n] = stride;
            stride *= numChoices[n];
        }
        
        numActives = new int[numCombinations];
        out.append ( "<td align=\"right\">active taclets</td>" );
        
        analyzeTaclets ();
        
        out.append ( "</tr>\n</thead>\n" );
        out.append ( "<tbody>\n" );
        
        writeChoiceTableBody (out);
        
        out.append ( "</tbody>\n" );
        out.append ( "</table>\n" );
    }
    
    private void analyzeTaclets () {
        final IteratorOfTacletModelInfo it = model.taclets();
        while ( it.hasNext () ) {
            final TacletModelInfo t = it.next ();
            final ListOfOptionModelInfo optionList = t.getOptions();
            analyzeTaclet ( optionList, 0, 0 );
        }
    }
    
    private void analyzeTaclet ( ListOfOptionModelInfo list, int line, int dim ) {
        if ( dim == options.length ) {
            numActives[line] += 1;
            return;
        }
        
        final int stride = strides[dim];
        OptionModelInfo[] choiceArray = options[dim];
        for ( int n = 0; n < choiceArray.length; n++ ) {
            if ( list.contains(choiceArray[n]) ) {
                analyzeTaclet ( list, line + stride*n, dim+1 );
                // there's at most one option from any category
                return;
            }
        }
        // no option from this category, so add to all
        for ( int n = 0; n < choiceArray.length; n++ ) {
            analyzeTaclet ( list, line + stride * n, dim+1 );
        }
    }

    private void writeChoiceTableBody (StringBuffer out) {
        for ( int line = 0; line < numCombinations; line++ ) {
            out.append ( "<tr>" );
            writeChoiceTableRow ( out, line, 0 );
            out.append ( "</tr>\n" );
        }
    }
    
    private void writeChoiceTableRow ( StringBuffer out, int line, int dim ) {
        if ( dim == options.length ) {
            out.append ( "<td align=\"right\">" + numActives[line] + "</td>" );
            return;
        }
        
        //System.out.println("line: "+line+", dim: "+dim);
        
        final int stride = strides[dim];
        if ( line % stride == 0 ) {
            final OptionModelInfo opt = options[dim][(line / stride) % options[dim].length];
            final String name = opt.name().toString();
            final int posColon = name.indexOf(':');
            final String shortName = name.substring(posColon+1);

            out.append("<td rowspan=\"" + stride + "\">"
                    + shortName + "</td>");
        }
        writeChoiceTableRow ( out, line, dim+1 );
    }
}
