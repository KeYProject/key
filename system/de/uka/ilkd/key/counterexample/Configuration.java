// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//

package de.uka.ilkd.key.counterexample;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.StringTokenizer;

/**
 * This class is the storage for global configuration data 
 * of the counterexample subpackage. In the future it might
 * even have a nice editable window instead of a configuration file
 *
 * You can use these to optimize your tests during runtime.
 * These configurations are stored in a separate textfile with
 * the name supplied by 'configfilename'
 * -Size of Domain
 * -Arguments to call Mgtp with
 * -which Axioms to use
 * -etc.
 *
 * @author Sonja Pieper
 * @version 0.1, created 08/08/01 
 */

public class Configuration {

    //the actual configuration data

    /**
     * Flag for use of the optimized axiom transformation
     */
    boolean optimize;

    /**
     * Flag which determines wether there is a lemma?
     */
    boolean test;

    /**
     * Number of constructors allowed in constructorterms
     */
    int domainmax;

    /**
     * Max number of parameters for which parameter rewriting 
     * will be generated
     */
    int maxargs;

    /**
     * String of ones and zeroes indicating which axioms to use
     */
    String useaxioms;

    /**
     * File in which to save the generated calculus for debugging f.e.
     */
    String filename;

    /**
     * Runtime parameters for the call of Mgtp, possible params: ext, verbose ...
     */
    String[] args;

    /**
     * Flag that determines wether to produce tex-output
     */
    boolean tex;

    /**
     * Name of the file in which all the configurations are stored now.
     */
    private String configfilename;


    /** 
     * creates a new configuration from the file specified by filename.
     * @param filename this should be the name of the file in which
     *                 your configuration is stored for example "max"
     */
    public Configuration(String filename){
	configfilename = filename;
    }


    /**
     * this method reads the configuration and stores it in the
     * respective fields. it is called by the constructor, so you
     * don't need to worry about it.
     */
    public void readConfig(){
	try{ 

	    RandomAccessFile raf = new RandomAccessFile(configfilename,"r"); 
	
	    //die configzeilen auslesen, s.o.:
	    domainmax= (new Integer(raf.readLine())).intValue();
	    String conf =              raf.readLine();
	    useaxioms=              raf.readLine();
	    maxargs  = (new Integer(raf.readLine())).intValue();
	    filename =              raf.readLine();
	    test     =             (raf.readLine()).startsWith("test");
	    optimize =             (raf.readLine()).startsWith("opt");
	    tex      =             (raf.readLine()).startsWith("tex");
	    raf.close();

	    //Debug Output:
	    System.out.println("Size of Domain is "+domainmax);
	    System.out.println("Mgtp Args are "+conf);
	    System.out.println("Rewriting "+maxargs+" Arguments");
	    System.out.println("Output will be saved to "+filename+".mg");

	    //Die Argumente muessen noch in einen Array 
	    //einsortiert werden:
	    StringTokenizer st = new StringTokenizer(conf,",");
	    args = new String[st.countTokens()+1];
	    args[0] = "ext"; //wichtig! Ist erforderlich fuer das Kalkuel
	    int i = 1;
	    while(st.hasMoreElements()){
		args[i] = st.nextToken();
		i++;
	    }

	    System.out.println("Arguments sorted.");
	}
	catch (FileNotFoundException e) {
	    System.out.println("Error getting max: Filenotfound");
	}
	catch (IOException e) {
	    System.out.println("Error reading max: Ausgabefehler");
	}

    }


    /**
     * with this method you can set all configuration data to default values.
     */
    public void setDefault(){
	domainmax = 2;
	args      = new String[1];
	args[0] = "ext";
	useaxioms = "11111111111111111111111111";
	maxargs   = 2;
	filename  = "default";
	test      = false;
	optimize  = true;
	tex       = false;
    }

    public void changeConfiguration(){//@@@ maybe with window one day in the future
	//do nothing now
    }
    
}
