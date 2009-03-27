// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.util.keydoc.html;


import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.FileNotFoundException;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.LinkedList;

import de.uka.ilkd.key.util.KeYResourceManager;



/** This class represents the director of the builder design pattern.
 It creates the datastucture, directs the KeYToHTMLBuilder and stores the 
 {@link de.uka.ilkd.key.util.keydoc.html.BoxedFile} it gets from the builder.
 */
class Director {
    
    String[] args;
    boolean rek=false;
    File currentFolder= new File(System.getProperty("user.dir"));
    //File startFolder= new File(System.getProperty("user.dir");

    private File[] toProcess; // Files to process
    private LinkedList allFolders= new LinkedList(); // The processed folders
    private LinkedList processed= new LinkedList(); // Already processed Files (In other folders).
    
    private final String docFolder="KeYDoc";
     
    
    /** Creates a new Director.*/
    public Director(String[] args, File currentFolder, boolean rek) {
    	//try {
    		this.args= args;
    		this.rek= rek;
    		this.currentFolder= currentFolder;
    /*	}
    	catch (IOException ioe) {
    		System.out.println(ioe + " occured, because your input pathname couldn't be resolved.");
    	}*/
    }
    
    /** Creates a new Director.*/
    public Director(String[] args, boolean rek) {
        this.args= args;
        this.rek= rek;
    }
    
    
    
    /* Should evaluate which key files should be documented and 
     * returned.
     */
    private File[] getKeYs(String[] which) {
    	KDFilenameFilter filter= new KDFilenameFilter(which);
    	try {
    		System.out.println("Looking for KeY Files in Folder " + currentFolder.getPath());
    		return currentFolder.listFiles(filter);
    	}
    	catch(Exception e) {
    		System.out.println("Exception while looking for matching files: " + e);
    		return null;
    	}
    	
    }    
    
    /** The main construction method.
     This method constructs the whole HTML data structure
     @return returns true if the files in this folders have been successfully built. (also false if there were no files to build)
     */
    private boolean construct() {
        try {
        	
                                        
            if (rek) {
            	Director d;
            	String[] foldersInDir= currentFolder.list(new FolderFilenameFilter(docFolder));
            	           	        	
            	for (int i=0; i<foldersInDir.length; i++) {		
            		if (!currentFolder/*.getCanonicalFile()*/.getName().equals(System.getProperty("user.dir")))
            			d= new Director(args, new File(currentFolder, foldersInDir[i]), rek);
            		else
            			d= new Director(args, new File(foldersInDir[i]), rek);
            		
            		LinkedList[] returnValue= d.constructAndReturn();
            		
            		for (int j=0; j< returnValue[0].size(); j++) {
            			ShortBox toSort= (ShortBox) returnValue[0].get(j);
            			sortInProcessed(toSort);           			
            		}   
            		
            		for (int j=0; j< returnValue[1].size(); j++) {
            			File toSort= (File) returnValue[1].get(j);
            			sortFileInLL(toSort, allFolders);           			
            		}   
                	
            	}            	
            	

            		
            }
            
            // Get the Files to process in this folder
            toProcess= getKeYs(args);
 
            
            if (toProcess== null)
                throw new NullPointerException(); 
            
            if (toProcess.length==0)
            	throw new Exception("No matches in folder: " + currentFolder.getName());
            
            BoxedFile htmlFile= null;	    

            StringBuffer thisstart=new StringBuffer();
            makeStartHeader(thisstart);
            StringBuffer thislinks= new StringBuffer();
            makeLinksHeader(thislinks, pathToName(currentFolder.getPath()));


            
            // Create thisindex.html
            String indexstr=("<html><head><title>KeYDoc Documentation</title></head><frameset cols=\"200,*\">  <!-- Frameset-Definition --><frameset rows=\"300,*\"><frame src=\"folders.html\" name=\"navigation\"><frame src=\"" + pathToName(currentFolder.getPath()) + "links.html\" name=\"navigation\"> </frameset> <!-- Frame-Window-Definition --> <frame src=\"" + pathToName(currentFolder.getPath()) + "start.html\" name=\"start\">   <!-- Frame-Window-Definition --><noframes><body><h1>No Frames</h1><p>Your Browser can't show frames.</p><p>KeYDoc is at the moment not fit to show KeY documentation on your Browser. Turn on frames to watch the KeYdoc.</p></body></noframes></frameset></html>");
            writeFile(docFolder + File.separator + pathToName(currentFolder.getPath()) + "index.html", indexstr);
            
//          Building the documentation Files and sorting them into the processed LinkedList.
            loop:
            for(int i=0; i<toProcess.length; i++) {
            	
            	System.out.println("Building file: " + toProcess[i].getName());
            	htmlFile= KDKeYToHTMLBuilder.buildHTMLFile(toProcess[i]);
            	  
              	if (htmlFile==null) // an Error occured during parsing. Skip this file
            		continue loop;
              	
              	String newFile= htmlFile.getFile().getName();
              	
              	// This monster extracts the first line of text out of the HTMLFile.
            	String shortDescription= htmlFile.getHtmlFile().getHTMLFileAsString().substring(htmlFile.getFirstOffset(), htmlFile.getFirstOffset()+htmlFile.getFirstLength());
            	
            	// Write Documentation File
            	// fileToWrite points to the file. It is relative to the path, there KeYDoc was started.
            	String fileToWrite= docFolder + File.separator + currentFolder.getPath() + File.separator + newFile; // the file, which should be written. Attention: without the .html ending! Search the file for .html for more explanation.
            	writeFile(fileToWrite + ".html", htmlFile.getHtmlFile().getHTMLFileAsString());
        	
            	String path= currentFolder.getPath() + File.separator + newFile;
            	path= path.substring(1, path.length());
            	
            	// Create thisstart.html
                thisstart.append("<tr><code><td class=\"left\" valign=\"top\"><code><a href=\"");
                thisstart.append(path +  ".html"); 
                thisstart.append("\">");
                thisstart.append(newFile); 
                thisstart.append("</a></td><td class=\"right\">");                
                thisstart.append(shortDescription);
                thisstart.append("</td></code></tr>");

                // Create thislinks.html
                thislinks.append("<a href=\"");
                thislinks.append(path + ".html");
                thislinks.append("\" target=\"start\">");
                thislinks.append(newFile);
                thislinks.append("</a><br>");
                
                ShortBox toSort= new ShortBox(new File(currentFolder.getPath() + File.separator + newFile), shortDescription);
                sortInProcessed(toSort);           

            }
            
            // Write thislinks and thisstart
            thislinks.append("</body></html>");
            writeFile(docFolder + File.separator + pathToName(currentFolder.getPath()) + "links.html", thislinks.toString());      
            thisstart.append("</table></center><br>");
            writeFile(docFolder + File.separator + pathToName(currentFolder.getPath()) + "start.html", thisstart.toString());
           	                                       
            return true;
        }
        catch(NullPointerException nPE) {     	
            return false;
        }
        catch(Exception e) {
        	System.out.println(e.getMessage());
        	return false;
        }
    }
    
    // returns a LinkedList of constructed ShortBoxes.
    private LinkedList[] constructAndReturn (){ 
    	boolean built= this.construct();
    	if (built)
    		sortFileInLL(currentFolder, allFolders);
    	
    	LinkedList[] ret= new LinkedList[2];
    	ret[0]= processed;   	


    	ret[1]= allFolders;
    	    	
    	return ret;
    }
    
    // this is the method called by keydoc. Starts construction and finishes it by building the "All Folders" files.
    public void startConstruct() {
    	
    	buildDataStructure();
    	
    	boolean built= this.construct();
    	if (built)
    		sortFileInLL(currentFolder, allFolders);
    	
        StringBuffer start=new StringBuffer();
        makeStartHeader(start);
        StringBuffer links= new StringBuffer();
        makeLinksHeader(links,"");
        StringBuffer folders= new StringBuffer();
        makeFoldersHeader(folders);       
	
        // Create folders.html
        for(int i=0; i<allFolders.size(); i++) {
        	File folder= (File) allFolders.get(i);
        	folders.append("<a href=\""+ pathToName(folder.getPath()) + "index.html\" target=\"_parent\">" + folder.getName() + "</a><br>");
        }
        folders.append("</body></html>");
        writeFile(docFolder + File.separator + "folders.html", folders.toString());         
        
        // Writing links in start.html, links.html
        ShortBox currentFile=null;
        for(int i=0; i<processed.size(); i++) {            
        	
        	currentFile= (ShortBox) processed.get(i);
        	String path= currentFile.getFile().getPath();
        	String name= currentFile.getFile().getName();
        	            
        	// Create start.html
            start.append("<tr><code><td class=\"left\" valign=\"top\"><code><a href=\"");
            start.append(path.substring(1, path.length()) + ".html"); 
            start.append("\">");
            start.append(name); // This is why the .html ending isn't attached right to the file.
            start.append("</a></td><td class=\"right\">");                
            start.append(currentFile.getDescription());
            start.append("</td></code></tr>");
            
            // Create links.html
            links.append("<a href=\"");
            links.append(path.substring(1, path.length()) + ".html");
            links.append("\" target=\"start\">");
            links.append(name);
            links.append("</a><br>");
            
        }
           
        links.append("</body></html>");
        writeFile(docFolder + File.separator + "links.html", links.toString());
              
        start.append("</table></center><br>");
        writeFile(docFolder + File.separator + "start.html", start.toString());
    	
    }
    
    private void copyLogo(String target) {
        KeYResourceManager.getManager().copyIfNotExists(Director.class, "logo/KeYLogo.png",
                target);
    }
     
        
    /* Create a file */
    private void writeFile(String name, String text) {
        
        File toWrite;
        FileWriter fw;
        BufferedWriter bw;
        
        try { 
        	toWrite= new File(name);
        	System.out.print("Writing file: " + toWrite.toString() +"...");
        	File neededFolders= toWrite.getParentFile();
        	neededFolders.mkdirs();
        	toWrite.createNewFile();
            fw = new FileWriter(toWrite); 
            bw = new BufferedWriter(fw); 
            bw.write(text); 
            bw.close(); 
            System.out.println(" done");
        }
        catch (FileNotFoundException fNFE) {
            System.out.println("FileNotFoundException: File not found or accessable.");
        }
        catch(IOException iOE) {
        	System.out.println("IOException occured during writing KeYdoc files.");
        }
        catch(Exception e) {
        	System.out.println("Exception: " + e);
        }
    }
    
    
    // Sorts the ShortBox toSort into the sorted processed Array, using binary search
    private void sortInProcessed(ShortBox toSort) {   	
    	
    	String newFile= toSort.getFile().getName();
        // Sort the file into the processed array
    	boolean sorted= false;
    	int last= processed.size()-1;
    	int first= 0;
    	int middle;
    	
    	String selFile;

    	if (processed.size()==0)
    		processed.add(toSort);
    	else
    		while (!sorted) {
    			
    			middle= first + (last-first)/2;
    			selFile= ((ShortBox) processed.get(middle)).getFile().getName();

    			if (newFile.compareToIgnoreCase(selFile)>0) {
    				if (processed.size()>middle+1) // index starts at 0.
    					if (newFile.compareToIgnoreCase(((ShortBox) processed.get(middle+1)).getFile().getName())>0)
    						first= middle+1;
    					else {
    						processed.add(middle+1, toSort);
    						sorted=true;
    					}            				
    				else {
    					processed.add(middle+1, toSort);
    					sorted=true;           					
    				}
    			}
    			else if (newFile.compareToIgnoreCase(selFile)<0) {
    				if (middle>0) // index starts at 0.
    					if (newFile.compareToIgnoreCase(((ShortBox) processed.get(middle-1)).getFile().getName())<0)
    						last=middle-1;
    					else {
    						processed.add(middle, toSort);
    						sorted= true;
    					}
    				else {
    					processed.add(middle, toSort);
    					sorted=true;
    				}
    			}
    			else {
    				processed.add(middle, toSort);
    				sorted= true;
    			}           				
    		}
        }
    
    // Sorts a File in a Linkedlist of File, using binary search
    private void sortFileInLL(File toSort, LinkedList list) {   	
    	
        // Sort the file into the list array
    	boolean sorted= false;
    	int last= list.size()-1;
    	int first= 0;
    	int middle;
    	
    	File selFile;

    	if (list.size()==0)
    		list.add(toSort);
    	else
    		while (!sorted) {
    			
    			middle= first + (last-first)/2;
    			selFile= (File) list.get(middle);

    			if (toSort.getName().compareToIgnoreCase(selFile.getName())>0) {
    				if (list.size()>middle+1) // index starts at 0.
    					if (toSort.getName().compareToIgnoreCase(((File) list.get(middle+1)).getName())>0)
    						first= middle+1;
    					else {
    						list.add(middle+1, toSort);
    						sorted=true;
    					}            				
    				else {
    					list.add(middle+1, toSort);
    					sorted=true;           					
    				}
    			}
    			else if (toSort.getName().compareToIgnoreCase(selFile.getName())<0) {
    				if (middle>0) // index starts at 0.
    					if (toSort.getName().compareToIgnoreCase(((File) list.get(middle-1)).getName())<0)
    						last=middle-1;
    					else {
    						list.add(middle, toSort);
    						sorted= true;
    					}
    				else {
    					list.add(middle, toSort);
    					sorted=true;
    				}
    			}
    			else {
    				list.add(middle, toSort);
    				sorted= true;
    			}           				
    		}
        }
    
    // Turns a pathname into a name for a file.
    private String pathToName(String path) {
    	String ret="";
    	for(int i=0; i< path.length(); i++)
    		if (path.charAt(i)!=File.separatorChar)
    			ret+= path.charAt(i);
    	
    	return ret;
    }
    
    
    /* Builds all the necessary folders and other files.
     */
    private void buildDataStructure() {
    	
    	
        File dir= new File(currentFolder, docFolder);
        System.out.print("Building folder: " + dir.toString() + "..."); 
        boolean success= dir.mkdir();
        if(!success)
            System.out.println("Warning: Directory couldn't be created. Does folder " + docFolder + " already exist?");
        else
        	System.out.println("done");
              
        // Create index.html
        String indexstr=("<html><head><title>KeYDoc Documentation</title></head><frameset cols=\"200,*\">  <!-- Frameset-Definition --><frameset rows=\"300,*\"><frame src=\"folders.html\" name=\"navigation\"><frame src=\"links.html\" name=\"navigation\"> </frameset> <!-- Frame-Window-Definition --> <frame src=\"start.html\" name=\"start\">   <!-- Frame-Window-Definition --><noframes><body><h1>No Frames</h1><p>Your Browser can't show frames.</p><p>KeYDoc is at the moment not fit to show KeY documentation on your Browser. Turn on frames to watch the KeYdoc.</p></body></noframes></frameset></html>");
        writeFile(docFolder + File.separator + "index.html", indexstr);                
        
    }
    
    private void makeStartHeader(StringBuffer start) {
        start.append("<html><head><title>KeYDoc start</title></head><body>");
        start.append("<center><table  border=\"1\" width=\"80%\"><tr><td colspan=\"1\" bgcolor=\"#BEBEFF\"><h2>Current Folder: ");
        start.append(currentFolder.getPath());
        start.append("</h2></td></tr></table><br><br>");
        start.append("<table  border=\"1\" width=\"80%\"><colgroup><col width=\"1*\"><col width=\"5*\"></colgroup><tr><td colspan=\"1\" bgcolor=\"#BEBEFF\"><h2>.key Summary</h2></td><td colspan=\"1\" bgcolor=\"#BEBEFF\">&#160;</td></tr>");
    }

	private void makeLinksHeader(StringBuffer links, String folder) {
		links.append("<html><head><title>KeYDoc links</title></head><body>");
		links.append("<br><a href=\"" + folder + "start.html\" target=\"start\">start</a><br><br>");
	}
	
	private void makeFoldersHeader(StringBuffer folders) {
		folders.append("<html><head><title>KeYDoc folders</title></head><body>");
		folders.append("<center><font size=\"7\"><font color=\"#008040\">K</font><font color=\"#0000FF\">e</font><font color=\"#008040\">Y</font></font><font size=\"0\">Doc</font></center><br><br>");
		folders.append("<a href=\"index.html\" target=\"_parent\">All folders</a><br><br>");
	}

}
	
// accepts all folders except the docfolder
class FolderFilenameFilter implements FilenameFilter {
	private String docFolder;
	
	public FolderFilenameFilter(String docFolder) {
		this.docFolder= docFolder;
	}
	
	public boolean accept(File dir, String name) {
		boolean ret= (new File(dir, name).isDirectory()) && !name.equals(docFolder);
		//System.out.println(name + " " + ret);
		return ret;
	}
}

// ShortBox boxes the Filename + Shortdescription.
class ShortBox {
	private File File;
	private String description;
	
	public ShortBox(File File, String description) {
		this.File= File;
		this.description= description;
	}
	
	public File getFile() {
		return File;
	}
	
	public String getDescription() {
		return description;
	}
}
