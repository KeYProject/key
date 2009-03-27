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

import de.uka.ilkd.key.rule.export.RuleExportModel;



public class HTMLTacletExporter {
    private RuleExportModel model = null;
    
    public HTMLTacletExporter() {
    }
    
    public void setModel(RuleExportModel model) {
        this.model = model;
    }
    
    public RuleExportModel getModel () {
        return model;
    }
    
    public void run (String outputDir) {
        HTMLModel htmlModel = new HTMLModel ( outputDir );
        HTMLContainer htmlContainer = htmlModel;
        
        HTMLFileIndex index = new HTMLFileIndex ( htmlModel, htmlContainer );
        HTMLFileByRuleSet byRuleSet = new HTMLFileByRuleSet ( htmlModel, htmlContainer );
        HTMLFileByDisplayName byDisplayName = new HTMLFileByDisplayName ( htmlModel, htmlContainer );
        HTMLFileByRuleName byRuleName = new HTMLFileByRuleName ( htmlModel, htmlContainer );
        HTMLFileByOption byChoice = new HTMLFileByOption ( htmlModel, htmlContainer );
        
        htmlModel.initAllFiles( model );
        
        htmlModel.writeAllFiles();
    }
    
}
