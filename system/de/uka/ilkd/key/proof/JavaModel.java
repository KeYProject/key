// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.io.File;
import java.text.DateFormat;
import java.util.Date;

public class JavaModel {

    private final String modelDir;
    private final String modelTag;
    private final String descr;
   
    public static final JavaModel NO_MODEL = new JavaModel();
   
    private JavaModel() {
	modelDir = null;
	modelTag = null;
	descr = "no model";
    }

    public JavaModel(String modelDir, String modelTag) {
	this.modelDir = (new File(modelDir)).getAbsolutePath();
	this.modelTag = modelTag;
	this.descr = "model "+(new File(modelDir)).getName()+"@"
	    +DateFormat.getTimeInstance(DateFormat.MEDIUM).format(new Date());
    }
   
    public String getModelDir() {
	return modelDir;
    }
   
    public String getModelTag() {
	return modelTag;
    }
   
    public boolean isEmpty() {
	return (this == NO_MODEL);
    }
   
    public String description() {
	return descr;
    }

    public boolean equals(Object o) {
	if (!(o instanceof JavaModel)) {
	    return false;
	} else if (getModelTag()==null) {
	    return ((JavaModel)o).getModelTag()==null;
	} else {
	    return (getModelTag().equals(((JavaModel)o).getModelTag()));
	}
    }
	

    public int hashCode() {
	if (getModelTag()==null) return 42;
	return getModelTag().hashCode();
    }
    
    public String toString() {
        return "---Program model---\nModel dir: "+modelDir+
	    "\nModel tag: "+modelTag+"\nDescription: "+descr;
    }
    
}
