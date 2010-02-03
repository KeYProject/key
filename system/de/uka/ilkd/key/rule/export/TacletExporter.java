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

package de.uka.ilkd.key.rule.export;

import java.io.File;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.export.html.HTMLTacletExporter;



public class TacletExporter {
    
    /** Option name for setting output directory. */
    private static String OPT_OUTPUTDIR = "-key-html-dir";
    /** Option name for omitting standard rules. */
    private static String OPT_NOSTANDARDRULES = "-key-no-standard-rules";
    
    private String outputDir;
    
    public void exportAll(TacletLoader l) {
        RuleExportModel model = new RuleExportModel ();
        l.addAllLoadedRules ( model );
        model.analyze ();
        
        HTMLTacletExporter exp = new HTMLTacletExporter();
        
        exp.setModel(model);
        
        if ( outputDir == null ) {
            outputDir = "html" + File.separatorChar;
        } else if ( outputDir.charAt(outputDir.length()-1) != File.separatorChar ) {
            outputDir = outputDir + File.separatorChar;
        }
        
        exp.run(outputDir);
    }
    
    public static void main ( String[] args ) {
	Main.configureLogger();
	
        final TacletLoader loader = new TacletLoader();
        final TacletExporter exporter = new TacletExporter();
        
        int n = 0;
        
        for (; n < args.length && args[n].startsWith("-"); n++) {
            final String argn = args[n];
            if (argn.equals(OPT_NOSTANDARDRULES)) {
                loader.setLoadStandardRules(false);
            }
            else if (argn.equals(OPT_OUTPUTDIR)) {
                n++;
                if (n < args.length) {
                	exporter.outputDir = args[n];
                } else {
                	System.err.println("Expected output directory after "+OPT_OUTPUTDIR);
                }
            }
        }
        
        if (loader.getLoadStandardRules()) {
            try {
                loader.loadFile("standardRules.key");
            } catch (ProofInputException e) {
                System.err.println("Loading of standard rules failed:\n"+e);
                return;
            }
        }
        
        exporter.exportAll(loader);
    }
}
