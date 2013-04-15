package de.uka.ilkd.key.util.rifl;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import javax.xml.parsers.*;

import org.xml.sax.*;
import org.xml.sax.helpers.*;

import recoder.ParserException;
import recoder.java.CompilationUnit;
import recoder.java.JavaProgramFactory;

import de.uka.ilkd.key.java.JavaReader;
import de.uka.ilkd.key.java.recoderext.ProofJavaProgramFactory;
import de.uka.ilkd.key.util.KeYExceptionHandler;


public class RIFLTransformer {

    private static final JavaProgramFactory jpf = ProofJavaProgramFactory.getInstance();
    private final XMLReader xmlReader;
    private List<CompilationUnit> javaCUs = new ArrayList<CompilationUnit>();

    private RIFLTransformer() throws ParserConfigurationException, SAXException {   
        SAXParserFactory spf = SAXParserFactory.newInstance();
        spf.setNamespaceAware(true);
        SAXParser saxParser = spf.newSAXParser();
        xmlReader = saxParser.getXMLReader();
        xmlReader.setContentHandler(new RIFLHandler());
        xmlReader.setErrorHandler(new RIFLHandler.ErrorHandler());
    }

    private void readRIFL (String fileName) throws IOException, SAXException {
        // TODO: validate input file
        xmlReader.parse(convertToFileURL(fileName));
        System.out.println("parsing finished");
    }
    
    public static void transform (String riflFilename, String javaSource, String savePath, KeYExceptionHandler kexh) {
        // step 1: parse RIFL file
        RIFLTransformer rt = null;
        try {
            rt = new RIFLTransformer();
        } catch (ParserConfigurationException e) {
            kexh.reportException(e);
        } catch (SAXException e) {
            kexh.reportException(e);
        }
        try {
            rt.readRIFL(riflFilename);
        } catch (IOException e) {
            kexh.reportException(e);
        } catch (SAXException e) {
            kexh.reportException(e);
        }
        
        // step 2: parse Java source
        try {
            rt.readJava(javaSource);
        } catch (IOException e) {
            kexh.reportException(e);
        } catch (ParserException e) {
            kexh.reportException(e);
        }
    }

    private void readJava(String source) throws IOException, ParserException {
        // TODO: collect all Java files at location
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

    /** Entry point for the stand-alone RIFL to JML* tool.
     */
    public static void main(String[] args) {
        final String riflFilename = "/tmp/test.xml";
        final String javaFilename = "/tmp/Test.java";
        RIFLTransformer.transform(riflFilename, javaFilename, null, SimpleRIFLExceptionHandler.INSTANCE);
    }
    
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

}
