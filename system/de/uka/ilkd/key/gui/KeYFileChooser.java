// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.io.File;

import javax.swing.JFileChooser;

public class KeYFileChooser {

    JFileChooser fileChooser;

    public KeYFileChooser() {
	fileChooser = new JFileChooser(new File(System.getProperty("user.dir")));
	fileChooser.setFileSelectionMode(JFileChooser.FILES_AND_DIRECTORIES);
	fileChooser.setFileFilter(new javax.swing.filechooser.FileFilter() {
		public boolean accept(File f) {
		    return 
			    f.isDirectory() 
			|| f.toString().endsWith(".key") 
			|| f.toString().endsWith(".java")
			|| f.toString().endsWith(".proof");
		}
		
		public String getDescription() {
		    return "KeY and JML files";
		}
	    });
    }

    public void prepare() {
        File selFile = fileChooser.getSelectedFile();
        if ((selFile != null) && selFile.isFile()) { // present & not dir.
            String filename = selFile.getAbsolutePath();    
	    if (!filename.endsWith(".proof")) 
                fileChooser.setSelectedFile(new File(filename+".proof")); 
        }
    }

    public void setDialogTitle(String title) {
	if (title!=null) {
	    fileChooser.setDialogTitle (title);
	} else {
	    fileChooser.setDialogTitle ("Select file to load");
	}
    }

    public boolean showSaveDialog(Main main) {
	int result = fileChooser.showSaveDialog(main);
	return (result == JFileChooser.APPROVE_OPTION);
    }

    public boolean showOpenDialog(Main main) {
	int result = fileChooser.showOpenDialog(main);
	return (result == JFileChooser.APPROVE_OPTION);
    }

    public File getSelectedFile() {
	return fileChooser.getSelectedFile();
    }

    public void selectFile(File f) {
	fileChooser.setSelectedFile(f);
    }


}
