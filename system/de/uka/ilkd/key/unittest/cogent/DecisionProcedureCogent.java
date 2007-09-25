// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.unittest.cogent;

import java.io.*;

public class DecisionProcedureCogent{

    public static CogentResult execute(String input) throws IOException{
	Process p = Runtime.getRuntime().exec
	    (new String[]{"rm", "-f", "/tmp/cogentOut"});
	try{
	    p.waitFor();
	}catch(InterruptedException e){
	    System.out.println(e);
	    //do nothing
	}
	File cogentOut = new File("/tmp/cogentOut");
	File file = File.createTempFile("key-cogent", null);
	PrintWriter out = new PrintWriter(new FileWriter(file));
	out.println(input);
	out.close();
	
	p = Runtime.getRuntime().exec
	    (new String[]{"cogent", file.getPath()/*+ " >/tmp/cogentOut"*/});
	InputStream error = p.getErrorStream();
	String response = read(error);
	InputStream in = p.getInputStream();
	response += read(in);
	try{
	    p.waitFor();
	}catch(InterruptedException e){
	    System.out.println(e);
	    //do nothing
	}
	in.close();
	error.close();
	
	file.delete();

	return new CogentResult(response);
    }  

    /** Read the input until end of file and return contents in a
     * single string containing all line breaks. */
    protected static String read ( InputStream in ) throws IOException {
        String lineSeparator = System.getProperty("line.separator");
        BufferedReader reader = new BufferedReader
            (new InputStreamReader(in));
        StringBuffer sb = new StringBuffer();
        String line;
        while ((line = reader.readLine()) != null) {
            sb.append(line).append(lineSeparator);
        }
        return sb.toString();
    }

}
