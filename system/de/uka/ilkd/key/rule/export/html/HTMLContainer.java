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

import java.io.File;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.rule.export.RuleExportModel;

public class HTMLContainer {
    private String rootFolder;
    
   // shown in navigation bar, initialized in first run
    private List fileList = new LinkedList();

    public HTMLContainer(String rootFolder) {
        this.rootFolder = rootFolder;
    }

    public String getRootFolder() {
        return rootFolder;
    }
    
    public void setRootFolder(String rootFolder) {
        this.rootFolder = rootFolder;
    }
    
    public void addFile(HTMLFile file) {
        //System.out.println("HTMLContainer.addFile(), "+file.getFilename());
        fileList.add(file);
    }
    
    public Iterator files () {
        return fileList.iterator();
    }
    
    public void initAllFiles ( RuleExportModel model ) {
        final Iterator it = files ();
        while ( it.hasNext () ) {
            HTMLFile file = (HTMLFile)it.next ();
            file.init ( model );
        }
    }
   
    public void writeAllFiles () {
        File f = new File(getRootFolder());
        if ( !f.exists() ) {
            if (!f.mkdirs()) {
                System.err.println("Could not create output directory:\n  "+getRootFolder());
                return;
            }
        } else {
            if (!f.isDirectory()) {
                System.err.println("Output path is not a a directory:\n  "+getRootFolder());
                return;
            }
        }
        final Iterator it = files ();
        while ( it.hasNext () ) {
            HTMLFile file = (HTMLFile)it.next ();
            //System.out.println ( "HTMLFile.write(), "+file.getFilename() );
            file.write ();
        }
    }
    
}
