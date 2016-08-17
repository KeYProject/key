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
 * <b>changes (weigl, 2016-08-16):</b>
 * changed interfaces to File. This avoid some crud string operations on filenames
 *
 * @author bruns
 * @author weigl, 2016-08-17
 */
public class RIFLTransformer {
    private final LinkedHashMap<CompilationUnit, String> javaCUs = new LinkedHashMap<CompilationUnit, String>();

    private RIFLTransformer() throws ParserConfigurationException, SAXException {
        JPF.initialize(new CrossReferenceServiceConfiguration());
        assert JPF.getServiceConfiguration() != null;
    }


    //private static final String TMP_PATH = System.getProperty("java.io.tmpdir");
    private static final JavaProgramFactory JPF =
            de.uka.ilkd.key.java.recoderext.ProofJavaProgramFactory.getInstance();

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
            final File riflFilename = new File(args[0]);
            final File javaFilename = new File(args[1]);
            RIFLTransformer.transform(riflFilename, javaFilename);
        }
    }

    /**
     * Transforms plain Java files + RIFL specification to Java+JML* specifications.
     *
     * @param riflFilename path to a RIFL file
     * @param javaSource   path to Java sources (should be a directory)
     * @param savePath     custom save path
     * @param kexh
     */
    public static void transform(File riflFilename, File javaSource,
                                 File savePath, KeYRecoderExcHandler kexh) {
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

    public static void transform(File riflFilename, File javaSource, KeYRecoderExcHandler kexh) {
        transform(riflFilename, javaSource, getDefaultSavePath(javaSource), kexh);
    }

    public static void transform(File riflFilename, File javaSource) {
        transform(riflFilename, javaSource, SimpleRIFLExceptionHandler.INSTANCE);
    }

    /**
     * Returns the default save path for transformed Java files.
     *
     * @param origSourcePath path to a directory or single Java file
     * @return path to the transformed directory
     */
    public static File getDefaultSavePath(File origSourcePath) {
        //TODO weigl: Shouldn't we use the old directory, because of reference to other java files?
        origSourcePath = getBaseDirPath(origSourcePath);
        return new File(origSourcePath.getParentFile(), origSourcePath.getName() + "_RIFL");
    }

    private static File getBaseDirPath(File origSourcePath) {
        if (origSourcePath.isFile())
            return origSourcePath.getParentFile();
        else
            return origSourcePath;
    }

    private void readJava(File root) throws IOException, ParserException {
        assert root.exists() : "source dir must exist";
        assert root.isDirectory() : "source must be directory";
        final DirectoryFileCollection files = new DirectoryFileCollection(root);
        final Walker walker = files.createWalker(".java");

        final ServiceConfiguration serviceConfiguration = JPF.getServiceConfiguration();

        // parse
        while (walker.step()) {
            final String javaFile = walker.getCurrentName();
            // debug
            // System.out.println("[RIFL] Read file: "+ javaFile);
            final CompilationUnit cu;
            Reader fr = null;
            try {
                fr = new BufferedReader(new FileReader(javaFile));
                cu = JPF.parseCompilationUnit(fr);
                javaCUs.put(cu, javaFile); // TODO: put absolute or relative path?
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

    private SpecificationContainer readRIFL(File fileName)
            throws IOException, SAXException, ParserConfigurationException {
        // TODO: validate input file
        final SAXParserFactory spf = SAXParserFactory.newInstance();
        spf.setNamespaceAware(true);

        SAXParser saxParser = spf.newSAXParser();
        XMLReader xmlReader = saxParser.getXMLReader();
        //xmlReader.setFeature("http://xml.org/sax/features/validation", true);
        xmlReader.setContentHandler(new RIFLHandler());
        xmlReader.setErrorHandler(new RIFLHandler.ErrorHandler());
        xmlReader.parse(new InputSource(new FileReader(fileName)));
        return ((RIFLHandler) xmlReader.getContentHandler()).getSpecification();
    }

    private void doTransform(final File riflFilename,
                             final File source,
                             final File savePath)
            throws IOException, SAXException, ParserException, ParserConfigurationException {
        ensureTargetDirExists(savePath);
        final File javaRoot = getBaseDirPath(source);

        // step 1: read files
        SpecificationContainer sc = readRIFL(riflFilename);
        readJava(javaRoot);

        // step 2: inject specifications
        for (final CompilationUnit cu : javaCUs.keySet()) {
            final SpecificationInjector si = new SpecificationInjector(sc, JPF.getServiceConfiguration().getSourceInfo());
            cu.accept(si);
        }

        // step 3: write modified Java files
        for (final Pair<CompilationUnit, String> javaUnit : javaCUs) {
            // TODO: javaCus contains absolute path, strip it
            final String onlyFilename = javaUnit.second.substring(javaUnit.second.lastIndexOf(File.separator) + 1);
            writeJavaFile(savePath, onlyFilename, javaUnit.first);
        }
    }

    private void ensureTargetDirExists(File target) throws IOException {
        if (target.exists()) {
            if (target.isDirectory() && target.canWrite()) {
                return; // nothing to do
            } else { // bad
                throw new IOException("target directory " + target + " not writable");
            }
        } else { // create directory
            target.mkdir();
        }
    }

    /**
     * Writes a single Java file.
     */
    private void writeJavaFile(File target, String fileName, CompilationUnit cu)
            throws IOException {
        FileWriter writer = null;
        final String filePath = target + File.separator + fileName;
        try {
            // System.out.println("[RIFL] Trying to write file "+filePath);
            writer = new FileWriter(filePath);
            final String source = cu.toSource();
            // System.out.println("[RIFL] Write the following contents to file:");
            // System.out.println(source);
            writer.append(source);
        } catch (final IOException e) {
            throw e;
        } finally {
            if (writer != null) writer.close();
        }
    }
}