// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//
//

package de.uka.ilkd.key.ocl.gf;


import java.io.*;
import java.net.URL;
import java.nio.channels.Channels;
import java.nio.channels.FileChannel;
import java.nio.channels.ReadableByteChannel;
import java.util.logging.Level;
import java.util.logging.Logger;

import de.uka.ilkd.key.util.KeYResourceManager;

/** @author Kristofer Johannisson and Hans-Joachim Daniels
 * handles the copying of GF OCL grammars from the resource directory
 * to a temporary directory (so that GF can access them) 
 */
class TempGrammarFiles {
    
    private final static Logger logger = Logger.getLogger(TempGrammarFiles.class.getName());
    final static String grammars2 = "grammars2";
    /**
     * for debugging, one might want to keep the generated grammar files
     */
    static boolean deleteOnExit = true;
    File oclgf2Dir = null;
    /**
     * a directory in the tmp directory with a unique name
     */
    File tempG2ParentDir = null;
    /** 
     * a directory in grammars2TempDir with name grammars2
     */
    File tempGrammars2Dir = null;
    final static String grammarFileListName = "grammars2list.txt"; 

    /** 
     * copy GF OCL grammars from internal resource directory to
     * a temporary directory, where GF can access them 
     */
    public TempGrammarFiles() throws IOException {
	    // attention: together with the KeYResourceHandler use "/" not
            // File.separator
            final URL grammarFileList = 
                KeYResourceManager.getManager().getResourceFile(TempGrammarFiles.class, 
                        grammars2 + "/" + grammarFileListName);
            
	    final BufferedReader listReader = 
	        new BufferedReader(new InputStreamReader
                        (grammarFileList.openStream()));	 
            
                        
	    //This is not really safe, so. could do sth. between delete and mkdir. 
	    tempG2ParentDir = File.createTempFile("grammars2_", null);
	    tempG2ParentDir.delete();
	    tempG2ParentDir.mkdir();
	    tempGrammars2Dir = new File (tempG2ParentDir.getPath() + File.separator + grammars2);
	    tempGrammars2Dir.mkdirs();
	    
	    int timer = 0;
	    for (String filename = 
	        listReader.readLine(); filename != null; filename = listReader.readLine()) {
                
                if (filename.startsWith(".")) {
                    filename = filename.substring(2, filename.length()); 
                }
                
                URL oldFileURL = KeYResourceManager.getManager().
	            getResourceFile(TempGrammarFiles.class, 
	                    grammars2 + "/" + filename);
	        if (oldFileURL == null) {
	            throw new FileNotFoundException
                        ("GF cannot be started due to a missing file ("+grammars2+"/"+filename+"). " +
                                        "Please ask the KeY team support@key-project.org for assistance.");	         
	        }
	        
                
                
                File newFile = new File (tempGrammars2Dir.getAbsolutePath() + File.separator + 
                        filename.replaceAll("/", File.separator));
                
	        if (logger.isLoggable(Level.FINER)) {
	            logger.finer("Copy: " + oldFileURL.getPath() + " --> " + newFile.getAbsolutePath());
	        }
	        if (!newFile.getParentFile().exists()) {
	            newFile.getParentFile().mkdirs();   
	        }
	        newFile.createNewFile();               
	        copyFile(new BufferedInputStream(oldFileURL.openStream()), 
                        newFile);
	    }
	    listReader.close();
    }

    /**
     * returns the location of the OCL-GF2 grammar files in the temp directory.
     * @return the location of the OCL-GF2 grammar files in the temp directory.
     */
    public String path2grammars2() {
        return tempGrammars2Dir.getAbsolutePath();
    }

    /**
     * creates a file with the given ocl constraint as the content and returns the handle.
     * Every call generates a new File.
     * @param ocl the constraint to be written
     * @return a File object representing the temporary file
     * @throws IOException
     */
    public static File createOCLtmp(String ocl) throws IOException{
        File result = File.createTempFile("ocl_", null);            

        PrintWriter toW = new PrintWriter(new BufferedWriter( new FileWriter(result)));
        toW.println(ocl);
        toW.close();
        perhapsDeleteOnExit(result);
        return result;
    }



    /**
     * If the flag deleteOnExit is set, the same named function will
     * be called on candidate
     * @param candidate the File that gets deleted on exit if set so
     */
    private static void perhapsDeleteOnExit(File candidate) {
        if (deleteOnExit) {
            try {
                candidate.deleteOnExit();
            } catch (SecurityException e) {
                logger.warning(e.getLocalizedMessage());
                e.printStackTrace();
            }
        }
    }

    /**
     * copies the content of src into dest
     * @param src the InputStream from where to read from
     * @param dest The destination File. Should dest already exist, it will get deleted first.
     * For that, it must not be a non-empty directory.
     * @throws IOException
     */
    private static void copyFile(InputStream src, File dest) throws IOException {       
        final int BLOCK_LENGTH=50000;
        final ReadableByteChannel inChannel = Channels.
        newChannel(new BufferedInputStream(src, BLOCK_LENGTH));

        if(dest.exists()) {
            dest.delete();
        }       

        final RandomAccessFile raf = new RandomAccessFile(dest, "rw");
        final FileChannel outChannel = raf.getChannel();

        long writtenBytes = -1;
        long position = 0;
        do {
            writtenBytes = outChannel.transferFrom(inChannel, position, BLOCK_LENGTH);
            if (writtenBytes > 0 && position>Long.MAX_VALUE-writtenBytes) {
                throw new RuntimeException("Cannot handle files greater than " + 
                        Long.MAX_VALUE + " bytes.");
            }
            position += writtenBytes;
        } while (writtenBytes >= BLOCK_LENGTH);
        inChannel.close();        
        outChannel.close();      
        raf.close();
    }
}
