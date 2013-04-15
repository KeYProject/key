package de.uka.ilkd.key.util.rifl;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import javax.xml.parsers.*;

import org.xml.sax.*;
import org.xml.sax.helpers.*;

import recoder.DefaultServiceConfiguration;
import recoder.ParserException;
import recoder.java.CompilationUnit;
import recoder.java.JavaProgramFactory;

import de.uka.ilkd.key.util.KeYExceptionHandler;


public class RIFLTransformer {

    private static final JavaProgramFactory jpf =
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
    
    
    /** Entry point for the stand-alone RIFL to JML* tool.
     */
    public static void main(String[] args) {
        final String riflFilename = "/tmp/test.xml";
        final String javaFilename = "/tmp/Test.java";
        final String targetFilename = "/tmp/TestNew.java";
        RIFLTransformer.transform(riflFilename, javaFilename, targetFilename, SimpleRIFLExceptionHandler.INSTANCE);
    }

    public static void transform (String riflFilename, String javaSource, String savePath, KeYExceptionHandler kexh) {
        RIFLTransformer rt = null;
        try {
            rt = new RIFLTransformer();
            rt.transform(riflFilename, javaSource, savePath);
        } catch (ParserConfigurationException e) {
            kexh.reportException(e);
        } catch (SAXException e) {
            kexh.reportException(e);
        } catch (ParserException e) {
            kexh.reportException(e);
        } catch (IOException e) {
            kexh.reportException(e);
            
        }
    }

    private final XMLReader xmlReader;
    private List<CompilationUnit> javaCUs = new ArrayList<CompilationUnit>();

    
    private RIFLTransformer() throws ParserConfigurationException, SAXException {   
        SAXParserFactory spf = SAXParserFactory.newInstance();
        spf.setNamespaceAware(true);
        SAXParser saxParser = spf.newSAXParser();
        xmlReader = saxParser.getXMLReader();
        xmlReader.setContentHandler(new RIFLHandler());
        xmlReader.setErrorHandler(new RIFLHandler.ErrorHandler());
        jpf.initialize(new DefaultServiceConfiguration());
        assert jpf.getServiceConfiguration() != null;
    }
    
    private void readJava(String source) throws IOException, ParserException {
        // TODO: collect all Java files from directory
        final Collection<String> javaFiles = new ArrayList<String>();
        javaFiles.add(source);
        
        // parse
        for (String javaFile: javaFiles) {
            final CompilationUnit cu;
            Reader fr = new BufferedReader(new FileReader(javaFile));
            cu = jpf.parseCompilationUnit(fr);
            javaCUs.add(cu);
        }
    }
    
    private void readRIFL (String fileName) throws IOException, SAXException {
        // TODO: validate input file
        xmlReader.parse(convertToFileURL(fileName));
    }

    private void transform(String riflFilename, String javaSource, String savePath) throws IOException, SAXException, ParserException {

        // step 1: parse RIFL file
        readRIFL(riflFilename);

        // step 2: parse Java source
        readJava(javaSource);

        // step 3: inject specifications
        for (CompilationUnit cu: javaCUs) {
            SpecificationInjector si = new SpecificationInjector();
            cu.accept(si);
        }

        // step 4: write modified Java files
        writeJavaFile(savePath,javaCUs.get(0));
    }
    
    /** Writes a single Java file. */
    private void writeJavaFile (String target, CompilationUnit cu) throws IOException {
        FileWriter writer = null;
        try {
            writer = new FileWriter(target);
            final String source = cu.toSource();
            System.out.println(source);
            writer.append(source);
        } catch (IOException e) {
            throw e;
        } finally {
            writer.close();
        }
    }

}
