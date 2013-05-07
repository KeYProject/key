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
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import javax.xml.parsers.*;

import org.xml.sax.*;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.ServiceConfiguration;
import recoder.java.CompilationUnit;
import recoder.java.JavaProgramFactory;

import de.uka.ilkd.key.util.KeYExceptionHandler;

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

    private static final JavaProgramFactory jpf = de.uka.ilkd.key.java.recoderext.ProofJavaProgramFactory
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

    private static final String testPath = "/home/daniel/rifl-test/";

    /**
     * Entry point for the stand-alone RIFL to JML* tool.
     */
    public static void main(String[] args) {
        final String riflFilename = testPath+"test.xml";
        final String javaFilename = testPath+"Test.java";
        final String targetFilename = testPath+"TestNew.java";
        RIFLTransformer.transform(riflFilename, javaFilename, targetFilename,
                SimpleRIFLExceptionHandler.INSTANCE);
    }

    public static void transform(String riflFilename, String javaSource,
            String savePath, KeYExceptionHandler kexh) {
        RIFLTransformer rt = null;
        try {
            rt = new RIFLTransformer();
            rt.transform(riflFilename, javaSource, savePath);
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

    private final XMLReader xmlReader;
    private final List<CompilationUnit> javaCUs = new ArrayList<CompilationUnit>();

    private RIFLTransformer() throws ParserConfigurationException, SAXException {
        final SAXParserFactory spf = SAXParserFactory.newInstance();
        spf.setNamespaceAware(true);
        final SAXParser saxParser = spf.newSAXParser();
        xmlReader = saxParser.getXMLReader();
        xmlReader.setContentHandler(new RIFLHandler());
        xmlReader.setErrorHandler(new RIFLHandler.ErrorHandler());
        jpf.initialize(new CrossReferenceServiceConfiguration());
        assert jpf.getServiceConfiguration() != null;
    }

    private void readJava(String source) throws IOException, ParserException {
        // TODO: collect all Java files from directory
        final Collection<String> javaFiles = new ArrayList<String>();
        javaFiles.add(source);

        final ServiceConfiguration serviceConfiguration = jpf.getServiceConfiguration();

        // parse
        for (final String javaFile : javaFiles) {
            final CompilationUnit cu;
            final Reader fr = new BufferedReader(new FileReader(javaFile));
            cu = jpf.parseCompilationUnit(fr);
            javaCUs.add(cu);
            serviceConfiguration.getChangeHistory().updateModel();
        }
    }

    private SpecificationContainer readRIFL(String fileName)
            throws IOException, SAXException {
        // TODO: validate input file
        xmlReader.parse(convertToFileURL(fileName));
        return ((RIFLHandler) xmlReader.getContentHandler()).getSpecification();
    }

    private void transform(String riflFilename, String javaSource,
            String savePath) throws IOException, SAXException, ParserException {

        // step 1: parse RIFL file
        final SpecificationContainer sc = readRIFL(riflFilename);

        // step 2: parse Java source
        readJava(javaSource);

        // step 3: inject specifications
        for (final CompilationUnit cu : javaCUs) {
            final SpecificationInjector si = new SpecificationInjector(sc,jpf.getServiceConfiguration().getSourceInfo());
            cu.accept(si);
        }

        // step 4: write modified Java files
        writeJavaFile(savePath, javaCUs.get(0));
    }

    /** Writes a single Java file. */
    private void writeJavaFile(String target, CompilationUnit cu)
            throws IOException {
        FileWriter writer = null;
        try {
            writer = new FileWriter(target);
            final String source = cu.toSource();
            System.out.println(source);
            writer.append(source);
        } catch (final IOException e) {
            throw e;
        } finally {
            writer.close();
        }
    }

}
