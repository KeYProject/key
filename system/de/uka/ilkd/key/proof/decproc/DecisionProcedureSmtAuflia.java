// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc;

import java.io.*;
import java.util.Map;
import java.util.WeakHashMap;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

import org.apache.log4j.*;

import de.uka.ilkd.key.gui.DecisionProcedureSettings;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.decproc.smtlib.Benchmark;


/** Represents a basic class for the invocation of decisison procedures accepting the SMT-LIB
 * format as input language on the translation of a KeY <tt>Goal</tt>.
 * <p>
 * An instance of this class takes a <tt>Goal</tt>, translates it in into a <tt>Benchmark</tt>
 * for the SMT logic (QF_)AUFLIA and stores this translation result in a temporary file.
 * <p>
 * This class is intended to be subclassed by classes which invoke a concrete decision procedure
 * supporting the SMT-LIB logic (QF_)AUFLIA. These subclasses must implement the provided hook method
 * <tt>execDecProc()</tt>
 * 
 * @author akuwertz
 * @version 1.3,  10/02/2006  (Extended to support quantifiers (AUFLIA) )
 */

public abstract class DecisionProcedureSmtAuflia extends AbstractDecisionProcedure {

    /* Additional fields */
    
    /* String constants for creation of the temporary file which stores the translation result */
    private static final String tempPrefix = "key_smt_auflia_";
    private static final String tempSuffix = ".smt";
    
    /* String constants for errors during file creation */
    private static final String tempFileCreateError = "Temporary file could not be created!\n";
    private static final String 
        problemFileCopyError = "*******************************************\n" + 
                               "An IOException occured during benchmark archiving!\n" +
                               "A problem file could not be copied!\n" +
                               "*******************************************";
    private static final String 
        archFileCreationError = "*******************************************\n" + 
                                "An IOException occured during benchmark archiving!\n" +
                                "Archive file could not be created!\n" +
                                "*******************************************";
    private static final String 
        zipArchiveCreationError = "*******************************************\n" + 
                                  "An IOException occured during benchmark archiving!\n" +
                                  "Problem could not be copied into a zipped archive!\n" +
                                  "*******************************************";
    private static final String
        problemPathFileCreationError = "*******************************************\n" + 
                                       "An IOException occured during benchmark archiving!\n" +
                                       "Problem path could not be written into file!\n" +
                                       "*******************************************";
    
    
    /** The <tt>Benchmark</tt> representing the translation result */
    private Benchmark resultBenchmark;
    
    /** The temporary file in which the translation result is stored */
    private final File tempFile;
    
    /** The <tt>File</tt> from with the current problem was loaded into KeY */
    private static File loadedProblem;
    
    /** The <tt>Proof</tt> that is currently selected in the proofer */
    private static Proof currentProof = null;
    
    /** A flag indicating that a new file was loaded */
    private static boolean newProblemLoaded;
    
    /** A <tt>String</tt> denoting the path of the directory in which the <tt>Benchmark</tt>s
     * created on the currently loaded problem will be archived  */
    private static String currentArchiveDir;
    
    /** */
    private static Map fromProofToArchive = new WeakHashMap();
        
    private static final String logPrefix = "smt_";
    private static final String logSuffix = "log";
    private static final String logDir = Config.KEY_CONFIG_DIR + File.separator + "SmtTrans_Logs";
    private static final String logFileCreateError = "SMT log file could not be created!\n";
    
    private static final String archiveDir = Config.KEY_CONFIG_DIR + File.separator + "SmtBench_Archive";
    private static final String archiveFileExt = ".smt";
    private static final String zipFileExt = ".zip";
    private static final String 
        notesAttrIntro = "\n This benchmark was translated from the following KeY sequent:\n" +
	                     " -----------------Begin sequent-----------------\n";
	private static final String 
		notesAttrOutro = " ------------------End sequent------------------\n" + " End of :notes";
    
    
    /** A <tt>Logger</tt> used to log the progress of the translation process.<br>
     * Serves as root for the logger hierarchy used during the translation process. It therefore
     * allows managing the configuration of all loggers in this hierarchy at a single point
     * 
     * @see #configureLogger(Level)
     */
    private static final Logger 
        logger = Logger.getLogger( DecisionProcedureSmtAuflia.class.getPackage().getName() );
    
    /** The pattern to format the output of log statements */
    private static final String layoutPattern = "%-5p [%-22c{1}]:  %m%n";
            
    
    
    /* Constructors */
    
    /** Mere constructor, just creates a new <tt>DecisionProcedureSmtAuflia</tt> instance
     *  
     * @param goal the <tt>Goal</tt> which should be translated
     * @param dptf the <tt>DecisionProcedureTranslationFactory</tt> used for translation
     * @param services the <tt>Services</tt> used during translation 
     */
    public DecisionProcedureSmtAuflia( Goal goal, DecisionProcedureTranslationFactory dptf,
                                       Services services ) {
        super( goal, null, dptf, services );
        try {   
            tempFile = File.createTempFile( tempPrefix, tempSuffix );
        } catch( IOException e ) {
            throw new RuntimeException( tempFileCreateError + e.getMessage() );
        }
    }
    
    
    
    /* Static methods */
    
    /** Informs this class that a new problem has been loaded in KeY.
     * <p>
     * This method should be called every time when a new problem has been loaded to the KeY prover.<br>
     * It delayedly sets up a new directory to store all benchmarks resulting from the loaded problem
     * 
     * @param problemFile the problem <tt>File</tt> the has been loaded 
     * @param proof the <tt>Proof</tt> that has been created for the given problem
     */
    public static void fireNewProblemLoaded( File problemFile, Proof proof ) {
        // If there is a previously loaded problem, save its context
        if ( currentProof != null ) {
            fireSelectedProofChanged( proof ); 
        } else {
            currentProof = proof;
        }
        loadedProblem = problemFile;
        newProblemLoaded = true;
        
    }
    
    
    /** Informs this class the another <tt>Proof</tt> has been selected in the prover. 
     * <p>
     * This method should be called every time when the selected <tt>Proof</tt> has changed.<br>
     * It changes the directory in which the created SMT-Lib benchmarks will be archived so that
     * all benchmarks resulting from one loaded problem will be stored in the same directory
     * 
     * @param proof the <tt>Proof</tt> that is currently selected in the prover 
     */
    public static void fireSelectedProofChanged( Proof proof ) {
        if ( currentProof != proof  &&  proof != null ) {
            // Save current settings:
            // If archive dir hasn't been created yet, put problem file into map
            if ( newProblemLoaded ) fromProofToArchive.put( currentProof, loadedProblem );
            // Else put the currently valid archive dir into map
            else fromProofToArchive.put( currentProof, currentArchiveDir );
            
            // Load new settings
            currentProof = proof;
            Object widget = fromProofToArchive.get( proof );
            // If the widget is a File, then the archive dir hasn't been created yet 
            if ( widget instanceof File ) {
                loadedProblem = (File) widget;
                newProblemLoaded = true;
                return;
            }    
            // If the widget is a String, retrieve the current archive dir
            if  ( widget instanceof String ) {
                currentArchiveDir = (String) widget;
                newProblemLoaded = false;
            }
            // if the widget is null, none of the above holds (in case of a newly loaded problem)
        }
    }
    
    
    
    /* Public and protected method implementations */
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.AbstractDecisionProcedure#run(boolean)
     */
    public DecisionProcedureResult run( boolean lightweight ) {
        return runInternal( null, lightweight );
    }
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.AbstractDecisionProcedure#runInternal(de.uka.ilkd.key.proof.decproc.ConstraintSet)
     */
    protected final DecisionProcedureResult runInternal( ConstraintSet constraintSet,
                                                         boolean lightWeight ) {
                       
        DecisionProcedureSettings currentDecprocSettings = 
            currentProof.getSettings().getDecisionProcedureSettings();
                
        // Translate given sequent
        logger.info( "Issuing new translation request at time: " + 
                     getCurrentDateString().substring( 11, 20 ) );
        SmtAufliaTranslation sequentTranslation = 
            dptf.createSmtAufliaTranslation( goal.sequent(), this.services, 
                                             currentDecprocSettings.useQuantifiers() );
        logger.info( "Retrieving translation result" );
        resultBenchmark = sequentTranslation.getBenchmark();
        DecisionProcedureResult result;
        
        // Check if a backend decision procedure should be called or only archiving is to be done
        if ( !currentDecprocSettings.useSMT_Translation() ) {

            // Backend decision procedure part
            try {    
                // Write result to file
                PrintWriter out = new PrintWriter( new FileWriter( tempFile ) );
                String input = resultBenchmark.toString();
                logger.info( "Storing result in tmp file: " +
                        tempFile.getName() );
                logger.debug( ">--------Created Benchmark--------<");
                logger.debug( input );
                logger.debug( ">----End of Created Benchmark-----<");
                out.println( input );
                out.close();
            } catch( IOException e ) {
                throw new RuntimeException( tempFileCreateError + e.getMessage() );
            }
            
            // Here follows the invocation of the used decision procedure, 
            // defined in an according subclass
            logger.info( "Invocating decision procedure..." );
            result = execDecProc();
            logger.info( "Decision procedure completed with result: " + 
                    ( result.getResult() ? "goal was closed!" : "goal could not be closed!" ) );
            logger.debug( "Decision procedure said in detail: " + result.getText() );
            logger.info( "Returning results to KeY prover!" );
            
            tempFile.delete();
            
        } else {
            result = new DecisionProcedureResult( false, "dummy result from mere translation",
                                                  Constraint.BOTTOM );
            logger.info( "Dummy Translation: created dummy result without calling a " +
                         "decision procedure");
        }
                
        
        // At last, archive the created benchmark
       
        if ( currentDecprocSettings.doBenchmarkArchiving() ||
             currentDecprocSettings.useSMT_Translation() ) {

            // If archiving of benchmarks is enabled, extend benchmarks with notes and archive them 
            logger.info( "Setting extended benchmark attributes" );
            resultBenchmark.setSource();
            resultBenchmark.setNotes( notesAttrIntro + goal.sequent().prettyprint(services) +	
                                      notesAttrOutro );
            if ( newProblemLoaded ) {
                // Create new archive dir and store problem in an appropriate way
                logger.info( "Newly loaded problem dectected: creating new current archive " +
                             "directory" );
                newProblemLoaded = false;
                currentArchiveDir = 
                    archiveDir + File.separator + getCurrentDateString().substring( 0 , 20 );
                File archDir = new File( currentArchiveDir );
                archDir.mkdirs();
                if ( loadedProblem.isDirectory() ) {
                    if ( ! currentProof.getSettings().getDecisionProcedureSettings()
                           .doZipProblemDir() ) {
                        // Just save path to problem...
                        logger.info( "Directory zipping disabled. Saving problem file path");
                        File pathFile = new File( archDir, loadedProblem.getName() );
                        try {
                            PrintWriter writer = new PrintWriter( new FileWriter( pathFile ) );
                            writer.println( loadedProblem.getAbsolutePath() );
                            writer.close();
                        } catch (IOException ioe ) {
                            System.out.println( problemPathFileCreationError );
                            ioe.printStackTrace();
                        }    
                    } else {
                        // ... or stored the zipped dir
                        logger.info( "Zipping and storing problem directory to archive file" );
                        File zipArchive = new File( archDir, loadedProblem.getName() + zipFileExt );
                        ArchiveZipper zipper = new ArchiveZipper( zipArchive, loadedProblem );
                        try {
                            zipper.zipDir();
                        } catch ( IOException ioe ) {
                            System.out.println( zipArchiveCreationError );
                            ioe.printStackTrace();
                        }
                    }
                    
                } else { 
                    // In all other cases store a copy of the loaded problem file
                    logger.info( "Copying problem file into current archive directory" );
                    copyFile( loadedProblem, archDir );
                }               
            }
            
            try {
                logger.info( "Creating benchmark archive file..." );
                String archiveFileName = currentArchiveDir + File.separator + "bm" + 
                new File( currentArchiveDir ).listFiles().length + archiveFileExt;
                File archiveFile = new File( archiveFileName );
                archiveFile.createNewFile();
                PrintWriter archiveWriter = new PrintWriter( new FileWriter( archiveFile ) );
                logger.info( "Storing benchmark in archive: " + archiveFileName );
                archiveWriter.println( resultBenchmark.toString() );
                archiveWriter.close();
            } catch (IOException e) {
                System.out.println( archFileCreationError );
                e.printStackTrace();
            }        
        }
        
        logger.info( ">>-------------------END-----------------------<<" );
        return result;
    }

    
    /** This method provides a hook for subclasses.<br>
     * It must be implemented by subclasses which execute a concrete decision procedure.
     * 
     * @return a <tt>DecisionProcedureResult</tt> representing the result of the execution of
     *         the decision procedure on the created and temporal stored <tt>Benchmark</tt>
     */
    protected abstract DecisionProcedureResult execDecProc();
    
    
    /** Returns the temporary <tt>File</tt> the translation result is stored in
     * @return the temporary <tt>File</tt> the translation result is stored in
     */
    protected File getTempFile() {
        return tempFile;
    }
    
    
    /** Returns the <tt>Benchmark</tt> that represents the translation result
     * @return the <tt>Benchmark</tt> representing the translation result
     */
    protected Benchmark getResultBenchmark() {
        return resultBenchmark;
    }
    
    
    /** Configures the <tt>Logger</tt> hierarchy used to log the process of translating
     * a <tt>Goal</tt> into SMT AUFLIA syntax.
     * <p>
     * If the specified <tt>Level</tt> is less or equal to <tt>INFO</tt>, a log file will be 
     * created in a log directory for SMT under the ".key" directory. All logged information
     * will be stored in this file, and not go to any inherited <tt>Appender</tt>s.<br>
     * Otherwise, no extra file will be created and all logged information output will go to 
     * any inherited <tt>Appender</tt>.
     * <p>
     * If this method is not called before calling any of the other methods of this class, the 
     * configuration of the <tt>Logger</tt> will be inherited from the rootlogger 
     *  
     * @param level the <tt>Level</tt> the <tt>Logger</tt> should be configured with
     * 
     * @throws RuntimeException if the specified <tt>Level</tt> is less or equal to <tt>INFO</tt>
     *                          and the log file could not be created
     */
    public static void configureLogger( Level level ) {
        logger.setLevel( level );
        if ( level == Level.DEBUG  ||  level == Level.INFO ) {
            try {
                // Assemble file name
                String filename = logDir + File.separator + logPrefix + 
                                  getCurrentDateString().substring( 0, 20 ) + "." + logSuffix;
                // Create directory and log file, if necessary
                new File( logDir ).mkdirs();
                new File( filename ).createNewFile();
                // add appender to logger
                Layout layout = new PatternLayout( layoutPattern );
                logger.addAppender( new FileAppender( layout, filename ) );
            } catch ( IOException e ) {
                throw new RuntimeException( logFileCreateError + e.getMessage() );
            }
            logger.setAdditivity( false );
        }
    } 
    
    
    
    /* Private helper methods */
    
    /** Creates a copy of a given file in the given target directory
     * @param original the <tt>File</tt> to be copied
     * @param targetDir the <tt>File</tt> denoting the target directory
     */
    private final void copyFile( File original, File targetDir ) {
        File copy = new File( targetDir, original.getName() );
        PrintWriter outCopy;
        FileReader inCopy;
        int chunkSize = 16 * 1024;
        char[] chunks = new char[ chunkSize ];
        boolean eof = false;
        try {
            copy.createNewFile();
            outCopy = new PrintWriter( new FileWriter( copy ) );
            inCopy = new FileReader( loadedProblem );
            try {
                while ( !eof ) {
                    int readChars = inCopy.read( chunks );
                    if ( readChars != -1 ) 
                        outCopy.println( new String( chunks, 0, readChars ) );
                    else eof = true; 
                }
            } catch ( IOException e ) {
                throw e;
            } finally {
                inCopy.close();
            }   
            outCopy.close();
        } catch ( IOException ioe ) {
            System.out.println( problemFileCopyError );
            ioe.printStackTrace();
        }
    }
    
    
    /** This class extends the operations on <tt>File</tt>s  by providing a zip operator for
     * directories.
     * <p>
     * This operator takes a <tt>File</tt> denoting a directory and zips its content into a
     * prior specified archive <tt>File</tt>
     * 
     * @author akuwertz
     */
    private class ArchiveZipper {
        
        /* Additional fields */
        
        /** The <tt>File</tt> denoting the zip archive to be created */
        private final File archiveFile;
        
        /** The <tt>File</tt> denoting the directory that should be zipped */
        private final File processedDir;
        
        private ZipOutputStream zipOut;
        
        /** The number of bytes being read from a (disc-) file into a buffer in one (java) step */
        private int readChunkSize = 16 * 1024;
                
        
        /* Constructors */
        
        /** Mere constructor. Constructs and configures a new <tt>ArchiveZipper</tt> instance
         * @param archive a <tt>File</tt> denoting the zip archive to be created
         * @param targetDir a <tt>File</tt> denoting the directory to be zipped 
         */
        public ArchiveZipper( File archive, File targetDir ) {
            archiveFile = archive;
            processedDir = targetDir;
        }
                
        
        /* Public setter and main methods */
        
        /** Sets the default compression method used for the target directory. It is initially set
         * to <tt>ZipOutputStream.DEFLATED</tt>.
         * 
         * @param method the default compression method
         * @throws IllegalArgumentException if the specified compression method is invalid
         * 
         * @see ZipOutputStream#setMethod(int)
         */
        public void setMethod( int method ) {
            zipOut.setMethod( method );
        }
        
        
        /** Sets the compression level used for the target directory if the compression
         * method is set to <tt>ZipOutputStream.DEFLATED</tt>. The default setting is 
         * <tt>DEFAULT_COMPRESSION</tt>
         *  
         * @param level the compression level (0-9)
         * @throws IllegalArgumentException if the compression level is invalid
         * 
         * @see ZipOutputStream#setLevel(int)
         */
        public void setLevel( int level ) {
            zipOut.setLevel( level );
        }
        
        
        /** Sets the number of bytes read from a file in a single processing step.<br>
         * This parameter is set to 16k per default, and can be adjusted for disc performance reasons
         * 
         * @param chunkSize the number of bytes read from a file in one step
         * 
         * @throws IllegalArgumentException if <tt>chunkSize</tt> is less or equal zero
         */
        public void setChunkSize( int chunkSize ) {
            readChunkSize = chunkSize;
        }
         
        
        /** Zips the target directory into the archive file
         *  
         * @throws IOException if the specified archive file could not be created or written to or 
         *         is no regular file or if the specified target directory could not be read from
         */
        public void zipDir() throws IOException {
            if ( ! archiveFile.exists() ) archiveFile.createNewFile();
            zipOut = new ZipOutputStream( new FileOutputStream( archiveFile ) );
            processDir( processedDir, processedDir );
            zipOut.close();
        }
        
        
        /* Private helper methods */
        
        /** Processes a given directory by zipping all contained files and recursively calling
         * itself on all contained directories
         * 
         * @param directory the <tt>File</tt> denoting the directory to be processed
         * @param rootDir the <tt>File</tt> denoting the root directory that should be zipped (by
         *                calling the <tt>zipDir()</tt> method)
         *                
         * @throws IOException if an IOError occurs during writing to the zipped archive or reading
         *                     from the source files 
         */
        private final void processDir( File directory, File rootDir ) throws IOException {
            File[] dirContents = directory.listFiles();
            String parentPath = rootDir.getParent() + File.separator;
            FileInputStream zipIn;
            byte[] chunks = new byte[ readChunkSize ];
            boolean eof = false;
            for ( int i = 0; i < dirContents.length; i++ ) {
                // Calculate hierarchical name the preserve tree structure in archive
                
                if ( dirContents[i].isDirectory() ) {
                    // Process this directory recursively
                    processDir( dirContents[i], rootDir );
                } else {
                    // Write file content into ZipEntry
                    String zipEntryName = dirContents[i].getPath().replaceFirst( parentPath, "" );
                    zipOut.putNextEntry( new ZipEntry ( zipEntryName ) );
                    zipIn = new FileInputStream( dirContents[i] );
                    eof = false;
                    while ( !eof ) {
                        int readChars = zipIn.read( chunks );
                        if ( readChars != -1 ) 
                            zipOut.write( chunks , 0 , readChars );
                        else eof = true; 
                    }
                    zipOut.closeEntry();
                }
            }
        }
        
    }
    
}
