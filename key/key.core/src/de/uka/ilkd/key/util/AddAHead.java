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

package de.uka.ilkd.key.util;

/**
 * Manages code of the KeY project, i.e. adds headers to the files and
 * removes an old one, but should be useable in other projects.
 *
 */
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Vector;

public class AddAHead {

    private static String[] endings=new String[]{"java","gjava","","html","g",
						 "jj","prj","key"};
    private String[] commentsstart=new String[]{"//","#","#","<!--","//","//",
						";;","//"};
    private String[] noendingFiles=new String[]{"Makefile"};
    private String[] commentsend=new String[]{"","","","-->","","","",""};
    private String[] notToRemove=new String[]{"#!/bin/sh", "<!DOCTYPE HTML",
					      ";; -*- Prcs -*-"};
    private String[] header;

    private String[] oldHeader=null;

    private File tmpFile=new File("TMP");

    private int[] countCode=initCounter();
    private int[] countComment=initCounter();
    private int[] countEmpty=initCounter();
    private int[] countFile=initCounter();
    private int[] countAddFile=initCounter();
    private int[] countRemoveFile=initCounter();


    public AddAHead() {
	
    }

    public BufferedReader getBufferedReader(File file) {
	try {
	    return new BufferedReader(new FileReader(file));
	} catch (IOException e) {
	    return null;
	}
    }

    public static int[] initCounter() {
	int[] result=new int[endings.length];
	for (int i=0; i<endings.length; i++) {
	    result[i]=0;
	}
	return result;
    }

    public String ending(String fn) {
	int l=fn.lastIndexOf(".");
	return (l>=0) ? fn.substring(l+1) : "";
    }

    public boolean startsWithOne(String s0, String[] s) {
        for (String value : s) {
            if (s0.startsWith(value)) return true;
        }
	return false;
    }

    public int containsHeader(File f, int type) throws IOException {
	BufferedReader b=getBufferedReader(f);	
	int i=0;
	int hStart=-1;
	int ohStart=-1;
	boolean h=false;
	boolean oh=false;
	boolean readComment=false;
	try {
	    while ( true) {
		String line=b.readLine();
		if (line==null) break;
		if (commentsstart[type].equals("//") && line.indexOf("/*")>=0){
		    readComment=true;
		}
		if ((line.indexOf(commentsstart[type])>=0 
		     && line.indexOf(commentsstart[type])<=5) || readComment) 
		    countComment[type]++;	        
		else if (line.equals("")) countEmpty[type]++;
		else countCode[type]++;
		if (commentsstart[type].equals("//") && line.indexOf("*/")>=0){
		    readComment=false;
		}
		if (h) continue;
		if (oh) continue;
		if (hStart>-1) {
		    if (line.equals(commentsstart[type]+header[i-hStart]
				    +commentsend[type])) {
			if (i-hStart==header.length-1) h=true;
		    } else {
			if (hStart>-1) hStart=-1;
		    }
		}
		if (line.equals(commentsstart[type]+header[0]
				+commentsend[type]) && hStart==-1) hStart=i;
		if (ohStart>-1) {
		    if (line.equals(commentsstart[type]+oldHeader[i-ohStart]
				    +commentsend[type])) {
			if (i-ohStart==oldHeader.length-1) oh=true;
		    } else {
			if (ohStart>-1) ohStart=-1;
		    }
		} 
		if (oldHeader!=null && line.equals(commentsstart[type]
						   +oldHeader[0]
						   +commentsend[type]) 
		    && ohStart==-1) ohStart=i;
		
		i++;
	    }
	} catch (IOException e) 
	    {Debug.out("Exception thrown by class AddAhead at IO");	    
	} finally {
	       b.close();  
	}
	if (h) return 2;
	if (oh) return 1;
	return 0;

    }

    public void addHeader(File f, int type) throws IOException {
	BufferedReader b=getBufferedReader(f);
	try {
	    PrintWriter w=new PrintWriter(new BufferedWriter
		(new FileWriter(tmpFile)));
	    String line=b.readLine();
	    if (line==null) {
	        w.close();
	        b.close();
	        return;
	    }
	    while (startsWithOne(line, notToRemove)) {	    
		w.println(line);
		line=b.readLine();
	    }
        for (String aHeader : header) {
            w.println(commentsstart[type] + aHeader + commentsend[type]);
        }
	    while (line!=null) {
		w.println(line);
		line=b.readLine();
	    }
	    w.close();
	} catch (IOException e) {
	    Debug.out("Exception thrown by class AddAhead at IO");
	} finally {
	       b.close();
	}
	tmpFile.renameTo(f);
    }

    public void removeOldHeader(File f, int type) throws IOException {
	BufferedReader b=getBufferedReader(f);
	PrintWriter w = null;
	try {
	    w=new PrintWriter(new BufferedWriter
		(new FileWriter(tmpFile)));
	    String line;
	    int i=0;
	    while ((line=b.readLine())!=null) {
		if (line.equals(commentsstart[type]+oldHeader[0]
				+commentsend[type])) {
		    String fline=line;
		    int hstart=i;
		    b.mark(80*10);
		    boolean oh=false;
		    while (!oh && line!=null 
			   && line.equals(commentsstart[type]
					  +oldHeader[i-hstart]
					  +commentsend[type])) {	    
			if (i-hstart==oldHeader.length-1) oh=true;
			line=b.readLine();
			i++;
		    }
		    if (!oh) {
			b.reset();
			line=fline;
		    }
		}
		if (line!=null) w.println(line);
		i++;
	    }
	} catch (IOException e) {
	    Debug.out("Exception thrown by class AddAhead at IO");
	} finally {
	    try { w.close(); } finally { b.close(); }
	}
	tmpFile.renameTo(f);
    }

    public void handleFile(File f) throws IOException {
	for (int i=0; i<endings.length; i++) {
	    if (ending(f.getName()).equals(endings[i])) {
		if (endings[i].equals("")) {
		    boolean ok=false;
            for (String noendingFile : noendingFiles) {
                if (noendingFile.equals(f.getName())) ok = true;
            }
		    if (!ok) return;
		}
		countFile[i]++;
		int ch=containsHeader(f, i);
		if (ch==0) {
		    addHeader(f, i);
		    countAddFile[i]++;
		} else if (ch==1) {
		    removeOldHeader(f, i);
		    addHeader(f, i);
		    countAddFile[i]++;
		    countRemoveFile[i]++;
		}
	    }
	}
    }

    public void visitFile(File currentFile) throws IOException {

	if (currentFile.isDirectory()) {
	    String[] fileList=currentFile.list();
        for (String aFileList : fileList) {
            visitFile(new File(currentFile.getPath()
                    + File.separator + aFileList));
        }
	} else {
	    if (currentFile.isFile()) { 
	        handleFile(currentFile);
	    }
	}	
    }
    public String summary(String ending, int countFile, int countRemoveFile, 
			  int countAddFile, int countCode, int countComment, 
			  int countEmpty) {
	int total=countCode+countComment+countEmpty;
	return "*** "+ countFile+" "+ending
	    +" *** \n The old header was removed in "+countRemoveFile
	    +" files.\n The new header was added to "+countAddFile
	    +" files.\n The files contained "+countCode+" lines of code, "
	    +countComment+" lines of comments, and " +countEmpty
	    +" empty lines.\n Sum of lines: "+total+".\n";	    
    }

    private static int sum(int[] is) {
	int result=0;
        for (int i1 : is) {
            result = result + i1;
        }
	return result;
    }
    
    public String statistics() {
	String s="";
	for (int i=0; i<endings.length; i++) {
	    s=s+summary("files ending with ."+endings[i], countFile[i], 
			countRemoveFile[i], 
			countAddFile[i], countCode[i], countComment[i], 
			countEmpty[i]);
	}	
	s=s+summary("files altogether", sum(countFile), sum(countRemoveFile), 
		    sum(countAddFile), sum(countCode), sum(countComment),
		    sum(countEmpty));
	return s;
    }

    public void readHeader(String f) {
	header=readLines(f);	
    }

    public String[] readLines(String f) {
	File file=new File(f);
	BufferedReader b=getBufferedReader(file);		
	Vector<String> v=new Vector<String>();
	String l;
	try{
	    while ((l=b.readLine())!=null) {
		v.add(l);
	    }
	    b.close();
	} catch(IOException e) {
	    System.out.println(e);
	}
	String[]  result=new String[v.size()];
	for (int i=0; i<result.length; i++) {
	    result[i]=v.elementAt(i);
	}
	return result;
    }

    public void readOldHeader(String f) {
	oldHeader=readLines(f);	
    }

    /**
     * searches files for old and new headers. If an old header is found,
     * the new one is inserted instead. If a new one is found, nothing
     * happens. Some statistics is finally printed. Comments signs are
     * used as in the commentsstart, commentsend arrays. Lines in
     * notToRemove are skipped and the header is inserted after them.
     *
     * @param args First parameter contains the file to start from. If it
     * is a directory all files below that directory are
     * considered. Second parameter is a String describing the file where
     * the new header can be found. This file should be text without any
     * comment characters. The Third parameter is the filename of the old
     * header that is to be replaced by the new header. The third one is
     * optional.
     *
     */
    public static void main(String args[]){
	AddAHead cm=(new AddAHead());
	System.out.println("AddAHead - adding headers to files in KeY.");
	System.out.println("ABSOLUTELY NO WARRANTY.\n");
	if (args.length<2) {
	    System.out.println("Usage: java AddAHead start header [oldheader]");
	    System.out.println("   adds headers (license text) to files or "
			       +"all files in directory.\n");
	    System.out.println("where start     is directory or file to look at "
			       +"license;");
	    System.out.println("      header    is text to use as header;");
	    System.out.println("      oldheader is header that is to be"
			       +" replaced.");
	    return;
	}
	cm.readHeader(args[1]);
	if (args.length>2) cm.readOldHeader(args[2]);
	try { 
	    cm.visitFile(new File(args[0]));
	} catch (IOException io) {
	    System.out.println("Error trying to access "+args[0]);
	}
	System.out.println(cm.statistics());
    }
}