package de.uka.ilkd.key.util.keydoc.html;

import java.io.File;
import java.io.IOException;

/** The main class of the keydoc Project.
 * 
 * @author sebastian 
 * It calls the director and tells him, which keyfiles he should process.
 */
public class KeYDoc {
    private Director d;   

    
    /** Make the documentation to a given set of .key files
     * 
     * @param args As paramaters the files to be documented are passed. i.e *.key for all key files in the folder, ex1.key ex2.key for the two .key files ex1 and ex2.
     */
    public void makeDoc(String[] args, boolean rek) {
 
        d= new Director(args, rek);
        d.startConstruct();
    }
    
    
    /** Make the documentation to a given set of .key files
     * 
     * @param args As paramaters the files to be documented are passed. i.e *.key for all key files in the folder, ex1.key ex2.key for the two .key files ex1 and ex2.
     */
    public void makeDoc(String[] args, String folder,  boolean rek) {
 
    	try {
        d= new Director(args, (new File(folder)).getCanonicalFile(), rek);
        d.startConstruct();
    	}
    	catch(IOException ioe) {
    		
    	}
    }
    
    /** The main method of the Keydoc project.
     * 
     * @param args As paramaters the files to be documented are passed. i.e *.key for all key files in the folder, ex1.key ex2.key for the two .key files ex1 and ex2.
     */
    public static void main(String[] args) {
    try {
        KeYDoc k = new KeYDoc();
    	
        if (args.length==0)
    		throw (new IllegalArgumentException("No files to process specified. Type runKeYDoc --h for more information."));
    	if (args[0].equals("--h") || args[0].equals("-h"))
            System.out.println("KeYDoc help:\nusage: runKeYDoc (files* | -r [folder])\n" +
                    "-r rekursive search. When searching rekursive, not specific files, " +
                    "but a folder must be specified. All .key and .proof files in this folder and all subfolders will be documented.");
        else if  (args[0].equals("-r")) { // only one folder can be passed for recursive treatment
            String[] argsnew= new String[2];
            argsnew[0]= "*.key"; argsnew[1]= "*.proof";
            k.makeDoc(argsnew, (args.length>1)? args[1] : System.getProperty("user.dir"), true);
        }
        else 
            k.makeDoc(args, false);
    	
    	System.out.println("KeYDoc finished.");
    }
    catch (IllegalArgumentException iAE) {
    	System.out.println(iAE.getMessage());  	    	
    }
    }
    
    
}
