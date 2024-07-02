// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof;

import java.io.File;
import java.text.DateFormat;
import java.util.Date;
import java.util.List;

import de.uka.ilkd.key.proof.init.Includes;

public final class JavaModel {

    private final String modelDir;
    private final String modelTag;
    private final String descr;
    private final String classPath;
    private final List<File> classPathEntries;
    private final String bootClassPath;
    private final String includedFiles;
    private final File initialFile;
   
    public static final JavaModel NO_MODEL = new JavaModel();
   
    
    
    /**
     * 
     */
    public static JavaModel createJavaModel(String javaPath,
                                      List<File> classPath,
                                      File bootClassPath,
                                      Includes includes,
                                      File initialFile) {
        JavaModel result;
        if(javaPath == null) {
            result = JavaModel.NO_MODEL;
        } else {
            result = new JavaModel(javaPath,
                                   classPath,
                                   bootClassPath,
                                   includes,
                                   initialFile);
        }
        return result;
    }
         
    
    private JavaModel() {
	modelDir = null;
	modelTag = null;
	descr = "no model";
	classPath = null;
   classPathEntries = null;
	bootClassPath = null;
	includedFiles = null;
	initialFile = null;
    }

    private JavaModel(String modelDir, 
	    	     List<File> classPathEntries,
	    	     File bootClassPath,
	    	     Includes includes,
	     	     File initialFile) {
	this.modelDir = (new File(modelDir)).getAbsolutePath();
	this.modelTag = "KeY_" + Long.valueOf((new java.util.Date()).getTime());
	this.descr = "model "+(new File(modelDir)).getName()+"@"
	    +DateFormat.getTimeInstance(DateFormat.MEDIUM).format(new Date());
	StringBuffer sb = new StringBuffer();
	if(classPathEntries != null && !classPathEntries.isEmpty()) {
	    for(File f : classPathEntries) {
		sb.append("\"" + f.getAbsolutePath() + "\", ");
	    }
	    sb.setLength(sb.length() - 2);
	}
	this.classPath = sb.toString();
	this.classPathEntries = classPathEntries;
	this.bootClassPath = bootClassPath == null 
	                     ? null 
	                     : bootClassPath.getAbsolutePath();
	StringBuffer sb2 = new StringBuffer();
	if(includes != null) {
		List<File> includeList = includes.getFiles();
		if(!includeList.isEmpty()) {
		    for(File f : includeList) {
				sb2.append("\"" + f.getAbsolutePath() + "\", ");
			    }
			    sb2.setLength(sb2.length() - 2);
	    }
	}
	includedFiles = sb2.toString();
	this.initialFile = initialFile;
    }
   
    public String getModelDir() {
	return modelDir;
    }
   
    public String getModelTag() {
	return modelTag;
    }
    
    public String getClassPath() {
	return classPath;
    }
    
    public List<File> getClassPathEntries() {
      return classPathEntries;
    }

   public String getBootClassPath() {
	return bootClassPath;
    }

   public String getIncludedFiles() {
	return includedFiles;
    }
   
    public File getInitialFile() {
      return initialFile;
    }

   public boolean isEmpty() {
	return this == NO_MODEL;
    }
   
    public String description() {
	return descr;
    }

    
    @Override    
    public boolean equals(Object o) {
       if (o == null || o.getClass() != this.getClass()) {
          return false;
       }       
       final JavaModel other = (JavaModel)o;       
       if(getModelTag() == null) {
          return other.getModelTag() == null;
       } else {
          return getModelTag().equals(other.getModelTag());
       }
    }
	

    @Override    
    public int hashCode() {
	if (getModelTag() == null) {
	    return 42;
	} else {
	    return getModelTag().hashCode();
	}
    }

    
    @Override
    public String toString() {
        return "---Program model---\nModel dir: "+modelDir+
	    "\nModel tag: "+modelTag+"\nDescription: "+descr;
    }
}