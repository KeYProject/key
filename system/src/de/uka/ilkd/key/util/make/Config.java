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


/** this class parses in a config file that has to use the following grammar:
 *  S -> (IDENTIFIER ':'  (alles ausser ';')* ';')* 
 *  then it creates files that can refer to the first IDENTIFIER by using
 *  "@IDENTIFIER@" that will be replaced by the expression after the ':'
 *  and before ';'
 */ 

package de.uka.ilkd.key.util.make;

import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Properties;

public class Config {

    private Config () {}

    private static final Config unique=new Config();

    //these two can't be made local to, say, GFinterface because of 
    //static loading
    public static File GF_PATH_FILE = new File
	(de.uka.ilkd.key.gui.configuration.PathConfig.getKeyConfigDir()+File.separator+"gf-path.props");

    public static final String GF_PATH_KEY = "[GFPath]";

    public static File SIMPLIFY_PATH_FILE = new File
	(de.uka.ilkd.key.gui.configuration.PathConfig.getKeyConfigDir()+File.separator+"simplify-path.props");

    public static final String SIMPLIFY_PATH_KEY = "[SimplifyPath]";

    
    static Map<String,StringBuffer> map = new LinkedHashMap<String,StringBuffer>();

    /** loads a resource and returns its URL 
     * @param cl the Class used to determine the resource 
     * @param resourcename the String that contains the name of the resource
     * @return the URL of the resource
     */
    public static URL getResourceFile(Class<?> cl, String resourcename) {
	URL resourceURL = cl.getResource(resourcename);
	if (resourceURL == null && cl.getSuperclass() != null) {
	    return getResourceFile(cl.getSuperclass(), resourcename);
	} else if (resourceURL == null && cl.getSuperclass() == null) {
	    return null;
	}
	return resourceURL;	
    }

    /** loads a resource and returns its URL 
     * @param o the Object used to determine the resource 
     * @param resourcename the String that contains the name of the resource
     * @return the URL of the resource
     */
    private static URL getResourceFile(Object o, String resourcename) {
	return getResourceFile(o.getClass(), resourcename);
    }

    /** reads until character char is found and return alls read signs without
     * character last */
    private static StringBuffer readUntil(InputStreamReader fr, char last) {
	StringBuffer result = new StringBuffer();
	try {
	    int chr = fr.read();
	    while (chr != -1 && ((char)chr)!=last) {
		if (((char)chr)!='\n' && ((char)chr)!='\r' &&
		    ((char)chr)!='\t') { //&& ((char)chr)!=' '
		    result.append((char)chr);
		}
		chr = fr.read();
	    } 	    
	} catch (IOException io) {
		System.err.println("Error occured while reading config file.");
		System.err.println(io);
		System.exit(-1);
	}	
	return result;
    }
    
    private static int readIdentifier(FileReader fr) {
	StringBuffer identifier = readUntil(fr,'[');
	if (identifier.length()==0) return -1;
	if (identifier.length()==0) {
	    throw new RuntimeException("IDENTIFIER EXPECTED.");
	}
	StringBuffer path = new StringBuffer();
	path = readUntil(fr,']');

	if (map.get(identifier.toString()) == null) {
	    map.put(identifier.toString(), path);
	}
	return 0;
    }

    private static void createFile(String filename, String template) {
	InputStreamReader fr = null;
	FileWriter fw = null;
	try {
	    fr = new InputStreamReader(getResourceFile(unique,template).openStream());   
   	    fw = new FileWriter(filename);	    
	    int chr = fr.read();	  
	    while (chr != -1) {
		if (((char)chr)!='@') {
		    fw.write(chr);
		} else {
		    StringBuffer res=readUntil(fr,'@');		    
		    if (map.get(res.toString()) == null) {
			System.err.println("Identifier "+res+" not defined");
			System.exit(-1);
		    }
		    String repl = map.get(res.toString()).toString() ;
		    fw.write(repl,0,repl.length());		    
		}
		chr = fr.read();		    
	    }
	} catch (IOException io) {
	    System.err.println("File "+filename+" can not be written.\n"+io);
	    System.exit(-1);	   
	} finally {
	        try {
	            if (fr != null) {
	                fr.close();
	            }
	            if (fw != null) {
	                fw.close();
	            }
            } catch (IOException e) {
                // ignore
            }
	    }
	}

    private static void writeToKeYConfig(File file, String header, 
					 String key, String prop) {
	if (!file.exists()) {
	    new File(de.uka.ilkd.key.gui.configuration.PathConfig.getKeyConfigDir()+File.separator).mkdir();
	}
	try {
            Properties props = new Properties();
            props.setProperty(key, prop);
            FileOutputStream out = 
                    new FileOutputStream(file);
            try { 
                props.store(out, header);
	    } finally {
	        out.close();
	    }
	} catch (Exception e) {
	    System.err.println("Could not write property to config file "+file);
	}
    }



    /** args[0] contains the file with the config infromation
     * args[1] if dev use development templates else dist templates
     */
    public static void main(String args[]) {
	FileReader fr = null;
	try {
	    fr = new FileReader(args[0]);       	
	    map = new LinkedHashMap<String, StringBuffer>();
	    while (readIdentifier(fr)!=-1) {	    
	    }
	    fr.close();
	} catch (IOException io) {
	    System.err.println("File "+args[0]+" not found");
	    System.exit(-1);
	}
	if ("dev".equals(args[1])) {
	    createFile("install_dev.key","install_dev.template");
	    createFile("Makefile.mk","config.template");
	    createFile("runTests","runTests.template");
	    createFile("runProver","runProver.template");	    
	    createFile("runJava","runJava.template");	    
	    createFile("miscConfigExtension","miscConfigExtension_dev.template");	    
	    if ("50".equals(args[2])) {
		createFile("startkey","startkey_dev_50.template");
	    } else if ("55".equals(args[2])) {
		createFile("startkey","startkey_dev_55.template");						
            } else {
		createFile("startkey","startkey_dev_60.template");				
		createFile("startkey.bat","startkey_60_bat.template");
	    }
	} else if ("dist".equals(args[1])) {    
	    createFile("install.key","install.template");
	    createFile("miscConfigExtension","miscConfigExtension.template");
	    if ("50".equals(args[2])) {
		createFile("startkey","startkey_50.template");
	    } else if ("55".equals(args[2])) {
		createFile("startkey","startkey_55.template");				
	    } else {
		createFile("startkey","startkey_60.template");	
		createFile("startkey.bat","startkey_60_bat.template");
	    }
	}
	createFile("configDefaultSnapShot","configDefaultSnapShot.template");
	if (args.length>3 && args[3]!=null && !("".equals(args[3]))) {
	    writeToKeYConfig(GF_PATH_FILE, "GF-Path-File",
			     GF_PATH_KEY, args[3]);
	}
	if (args.length>4 && args[4]!=null && !("".equals(args[4]))) {
	    writeToKeYConfig(SIMPLIFY_PATH_FILE, "Simplify-Path-File",
			     SIMPLIFY_PATH_KEY, args[4]);
	}
    }
}
