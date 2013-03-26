// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.MalformedURLException;
import java.net.URL;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.KeYResourceManager;

public class RuleSource {

    private static final String PATH_TO_RULES = "rules/";

    private URL url=null;

    private File f=null;

    private long numberOfChars;

    private RuleSource(File f) {
	this.f=f;
	if (f!=null) {
	    numberOfChars=f.length();
	}
    }


    private RuleSource(URL url) {
	this.url = url;
	if (url.getProtocol().equals("file")) {
	    numberOfChars = (new File(url.getFile())).length();
	} else {
	    try {
		InputStream input = url.openStream();
		numberOfChars=0;
		int i=input.read();
		while (i!=-1){
		    numberOfChars++;
		    i=input.read();
		}
		input.close();
	    } catch (IOException ioex){
		System.err.println("IOException in class RuleSource");
	    }
	}
    }
   

    public static RuleSource initRuleFile(String filename) {
        URL u = KeYResourceManager.getManager().
            getResourceFile(Proof.class, PATH_TO_RULES + filename);
        if (u == null) {
            // a more specific exception type would probably be better
            throw new RuntimeException("Could not find rule file "+PATH_TO_RULES+filename);
        }
	return new RuleSource(u);
    }

    public static RuleSource initRuleFile(URL url) {
	return new RuleSource(url);
    }
    
    
    public int getNumberOfChars(){
	return (int)numberOfChars;
    }

    public static RuleSource initRuleFile(File file) {
	return new RuleSource(file);
    }
   
    public File file() {
	if (f==null) {
	    return new File(url.getFile());
	} else {
	    return f;
	}
    }
    
    public String getInclusionString() {
        return "\\includeFile \""+file().getAbsolutePath()+"\";\n";
    }

   public String toString() {
       if (url!=null) {
	   return url.toString();
       } else {
	   return f.toString();
       }
   }

   public String getExternalForm() {
       URL localURL = null;
       if (f==null) {
           localURL = url; 
       } else {
           try {
               localURL = f.toURI().toURL();
           } catch (MalformedURLException e) {
               return null;
           }
       }
       return localURL.toExternalForm(); 
   }    
   
    public InputStream getNewStream() {
	try {
	    if (f==null) {
		return url.openStream();
	    } else {
		return new FileInputStream(f);
	    }
	}
	catch (IOException ioe) {
	    System.err.println("*******************************************");
	    System.err.println("IO-Error occured while opening rule stream.");
	    System.err.println("URL: "+url);
	    System.err.println(ioe);
	    System.err.println("*******************************************");
	    ioe.printStackTrace();
	    throw new RuntimeException("Error while parsing rules.", ioe);
	}
    }
	

    public boolean isDirectory() {       
	return file().isDirectory();
    }

    public boolean isAvailable() {
        InputStream is = null; 
        try {
            is = getNewStream();
        } catch (RuntimeException re) {           
            return false;
        } finally {
            if (is != null) {
        	try {
	            is.close();
                } catch (IOException e) {
                    return false;
                }
            }
        }
        return is != null;
    }
}
