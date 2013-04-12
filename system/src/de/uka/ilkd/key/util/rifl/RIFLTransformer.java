package de.uka.ilkd.key.util.rifl;

import java.io.File;
import java.io.IOException;

import javax.xml.parsers.*;
import org.xml.sax.*;
import org.xml.sax.helpers.*;


public class RIFLTransformer {
    
    private final XMLReader xmlReader;

    private RIFLTransformer() throws Exception {   
        SAXParserFactory spf = SAXParserFactory.newInstance();
        spf.setNamespaceAware(true);
        SAXParser saxParser = spf.newSAXParser();
        xmlReader = saxParser.getXMLReader();
        xmlReader.setContentHandler(new RIFLHandler());
        xmlReader.setErrorHandler(new RIFLHandler.ErrorHandler());
    }
    
    private void readRIFL (String fileName) {
        try {
            // TODO: validate input file
            xmlReader.parse(convertToFileURL(fileName));
            System.out.println("parsing finished");
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (SAXException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    /** Entry point for the stand-alone RIFL to JML* tool.
     * 
     * @param args
     */
    public static void main(String[] args) {
        // evaluate parameters
        try {
            RIFLTransformer rt = new RIFLTransformer();
            rt.readRIFL("/tmp/test.xml");
        } catch (Exception e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        
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
