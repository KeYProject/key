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

package de.uka.ilkd.key.util.rifl;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Reader;
import javax.xml.parsers.*;
import org.xml.sax.*;
import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.ServiceConfiguration;
import recoder.java.CompilationUnit;
import recoder.java.JavaProgramFactory;
import de.uka.ilkd.key.util.DirectoryFileCollection;
import de.uka.ilkd.key.util.FileCollection.Walker;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.Pair;

/**
 * Facet class for interpreting RIFL specifications. The Requirements for
 * Information Flow Language (RIFL) is a tool-independent specification language
 * developed in the RS3 project. Method <code>transform</code> reads a RIFL file
 * and Java sources and writes JML* information flow specifications to the
 * original Java files.
 *
 * @author bruns
 */
public class RIFLTransformer {

    private static final String TMP_PATH = System.getProperty("java.io.tmpdir");
    private static final JavaProgramFactory JPF = de.uka.ilkd.key.java.recoderext.ProofJavaProgramFactory
            .getInstance();

    private static String convertToFileURL(String filename) {
        String path = new File(filename).getAbsolutePath();
        if (File.separatorChar != '/') {
            path = path.replace(File.separatorChar, '/');
        }

        if (!path.startsWith("/")) {
            path = "/" + path;
        }
        return "file:" + path;
    }

    /**
     * Entry point for the stand-alone RIFL to JML* tool.
     */
    public static void main(String[] args) {
        if (args.length < 2 || "--help".equals(args[0])) {
            System.out.println("This is the RIFL to JML* transformer.");
            System.out.println("Usage: <RIFL file> <Java sources>");
        } else {
            final String riflFilename = args[0];
            final String javaFilename = args[1];
            RIFLTransformer.transform(riflFilename, javaFilename);
        }
    }

    /**
     * Transforms plain Java files + RIFL specification to Java+JML* specifications.
     * @param riflFilename path to a RIFL file
     * @param javaSource path to Java sources (should be a directory)
     * @param savePath custom save path
     * @param kexh
     */
    public static void transform(String riflFilename, String javaSource,
            String savePath, KeYRecoderExcHandler kexh) {
        assert riflFilename != null;
        assert javaSource != null;
        assert savePath != null;
        assert kexh != null;

        RIFLTransformer rt = null;
        try {
            rt = new RIFLTransformer();
            rt.doTransform(riflFilename, javaSource, savePath);
        } catch (final ParserConfigurationException e) {
            kexh.reportException(e);
        } catch (final SAXException e) {
            kexh.reportException(e);
        } catch (final ParserException e) {
            kexh.reportException(e);
        } catch (final IOException e) {
            kexh.reportException(e);

        }
    }

    public static void transform(String riflFilename, String javaSource, KeYRecoderExcHandler kexh) {
        transform(riflFilename, javaSource, getDefaultSavePath(javaSource), kexh);
    }

    public static void transform(String riflFilename, String javaSource) {
        transform(riflFilename, javaSource, SimpleRIFLExceptionHandler.INSTANCE);
    }

    private final XMLReader xmlReader;
    private final LinkedHashMap<CompilationUnit,String> javaCUs
            = new LinkedHashMap<CompilationUnit,String>();

    private RIFLTransformer() throws ParserConfigurationException, SAXException {
        final SAXParserFactory spf = SAXParserFactory.newInstance();
        spf.setNamespaceAware(true);
        final SAXParser saxParser = spf.newSAXParser();
        xmlReader = saxParser.getXMLReader();
        xmlReader.setContentHandler(new RIFLHandler());
        xmlReader.setErrorHandler(new RIFLHandler.ErrorHandler());
        JPF.initialize(new CrossReferenceServiceConfiguration());
        assert JPF.getServiceConfiguration() != null;
    }

    /**
     * Returns the default save path for transformed Java files.
     * @param origSourcePath path to a directory or single Java file
     * @return path to the transformed directory
     */
    public static String getDefaultSavePath (String origSourcePath) {
        origSourcePath = getBaseDirPath(origSourcePath);
        final String[] path = origSourcePath.split(File.separator);
        final String dirName = "".equals(path[path.length-1])? path[path.length-2]: path[path.length-1];
        final String result = TMP_PATH + File.separator + dirName + ".rifl";
        return result;
    }

    private static String getBaseDirPath(String origSourcePath) {
        if (origSourcePath.endsWith(".java")) {
            // select containing directory
            final String absPath = new File(origSourcePath).getAbsolutePath();
            origSourcePath = absPath.substring(0, absPath.lastIndexOf(File.separator));
        }
        return origSourcePath;
    }

    private void readJava(String source) throws IOException, ParserException {

        final File root = new File(source);
        assert root.exists(): "source dir must exist";
        assert root.isDirectory(): "source must be directory";
        final DirectoryFileCollection files = new DirectoryFileCollection(root);
        final Walker walker = files.createWalker(".java");

        final ServiceConfiguration serviceConfiguration = JPF.getServiceConfiguration();

        // parse
        while (walker.step()) {
            final String javaFile = walker.getCurrentName();
            System.out.println("[RIFL] read file: "+ javaFile); // XXX
            final CompilationUnit cu;
            Reader fr = null;
            try {
                fr = new BufferedReader(new FileReader(javaFile));
                cu = JPF.parseCompilationUnit(fr);
                javaCUs.put(cu,javaFile); // TODO: put absolute or relative path?
                serviceConfiguration.getChangeHistory().updateModel(); // workaround to an issue in recoder
            } catch (IOException e) {
                throw e;
            } catch (ParserException e) {
                throw e;
            } finally {
                if (fr != null) fr.close();
            }
        }
    }

    private SpecificationContainer readRIFL(String fileName)
            throws IOException, SAXException {
        // TODO: validate input file
        xmlReader.parse(convertToFileURL(fileName));
        return ((RIFLHandler) xmlReader.getContentHandler()).getSpecification();
    }

    private SpecificationContainer sc = null;
    private Exception threadExc = null;

    private void doTransform(final String riflFilename, String source, String savePath)
            throws IOException, SAXException, ParserException {

        // step 1a: parse RIFL file
        final Runnable r = new Runnable () {
             public void run() {
                 System.out.println("[RIFL] start RIFL reader"); // XXX
                 try {
                     sc = readRIFL(riflFilename);
                     // debug
                     System.out.println(sc);
                 } catch (Exception e) {
                     threadExc = e;
                 } finally {
                     System.out.println("[RIFL] finished RIFL reader"); // XXX
                 }
             }
        };
        final Thread riflReader = new Thread(r,"RIFLReader");
        riflReader.start();

        // step 1b: parse Java source
        final String javaRoot = getBaseDirPath(source);
        final Runnable t = new Runnable() {
            public void run() {
                System.out.println("[RIFL] start Java reader"); // XXX
                try {
                    readJava(javaRoot);
                } catch (Exception e) {
                    threadExc = e;
                } finally {
                    System.out.println("[RIFL] finished Java reader"); // XXX
                }
            }
        };
        final Thread javaReader = new Thread(t,"JavaReader");
        javaReader.start();

        // synchronize
        while (riflReader.isAlive() || javaReader.isAlive()) {}
        // promote exceptions
        if (threadExc instanceof RuntimeException) throw (RuntimeException)threadExc;
        if (threadExc instanceof IOException) throw (IOException)threadExc;
        if (threadExc instanceof SAXException) throw (SAXException)threadExc;
        if (threadExc instanceof ParserException) throw (ParserException)threadExc;


        // step 2: inject specifications
        for (final CompilationUnit cu : javaCUs.keySet()) {
            final SpecificationInjector si = new SpecificationInjector(sc,JPF.getServiceConfiguration().getSourceInfo());
            cu.accept(si);
        }

        // step 3: write modified Java files
        ensureTargetDirExists(savePath);
        for (final Pair<CompilationUnit,String> javaUnit: javaCUs) {
            // TODO: javaCus contains absolute path, strip it
            final String onlyFilename = javaUnit.second.substring(javaUnit.second.lastIndexOf(File.separator)+1);
            writeJavaFile(savePath, onlyFilename, javaUnit.first);
        }
    }

    private void ensureTargetDirExists(String target) throws IOException {
        final File file = new File(target);
        if (file.exists()) {
            if (file.isDirectory() && file.canWrite()) {
                return; // nothing to do
            } else {
                // bad
                throw new IOException("target directory "+target+" not writable");
            }
        } else { // create directory
            file.mkdir();
        }
    }

    /** Writes a single Java file. */
    private void writeJavaFile(String target, String fileName, CompilationUnit cu)
            throws IOException {
        FileWriter writer = null;
        final String filePath = target + File.separator + fileName;
        try {
            System.out.println("[RIFL] Trying to write file "+filePath); // XXX
            writer = new FileWriter(filePath);
            final String source = cu.toSource();
            System.out.println("[RIFL] write the following contents to file:"); // XXX
            System.out.println(source);
            writer.append(source);
        } catch (final IOException e) {
            throw e;
        } finally {
            if (writer != null) writer.close();
        }
    }

}
