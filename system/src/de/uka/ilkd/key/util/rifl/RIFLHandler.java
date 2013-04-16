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

import java.util.HashMap;
import java.util.Map;

import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;
import org.xml.sax.helpers.DefaultHandler;

import static de.uka.ilkd.key.util.rifl.SpecificationEntity.*;
import static de.uka.ilkd.key.util.MiscTools.apply;

/** XML content handler for the RIFL language.
 * Produces a RIFL {@link SpecificationContainer}.
 * May throw obscure exceptions on non-wellformed XML documents.
 * @author bruns
 */
class RIFLHandler extends DefaultHandler {
    
    private final static String DEFAULT_CATEGORY = "Spider Pig";
    private final static String DEFAULT_DOMAIN = "low";
    
    private final Map<SpecificationEntity,String> sources2categories =
            new HashMap<SpecificationEntity,String>();
    private final Map<SpecificationEntity,String> sinks2categories =
            new HashMap<SpecificationEntity,String>();
    private final Map<String,String> categories2domains = 
            new HashMap<String, String>();
    
    
    private Map<SpecificationEntity,String> tmpMap = null;
    private String category = DEFAULT_CATEGORY;
    
    
    public RIFLHandler() {
        categories2domains.put(DEFAULT_CATEGORY, DEFAULT_DOMAIN);
    }
    
    
    public SpecificationContainer getSpecification() {
        // drop categories, merge sources and sinks
        final Map<SpecificationEntity,String> tmp =
                new HashMap<SpecificationEntity,String>();
        tmp.putAll(apply(sources2categories,categories2domains));
        tmp.putAll(apply(sinks2categories,categories2domains));
        return new DefaultSpecificationContainer(tmp);
    }
    
    // XXX follows format suggested by Matthias Perner et al.

    @Override
    public void startElement(String uri, String localName, String qName, Attributes attributes) {
        // debug
        System.out.println(uri+" : "+localName+" : "+qName+" : "+printAttributes(attributes));
        
        switch (localName) {
        case "sources": startSources(); break;
        case "sinks": startSinks(); break;
        case "category": setCategory(attributes); break;
        case "assign": assignCategory(attributes); break;
        case "field": putField(attributes); break;
        case "parameter": putParam(attributes); break;
        case "returnvalue": putReturn(attributes); break;
        default:
        }
    }
    
    @Override
    public void endDocument () {
        // TODO: consistency validation
    }

    private void putReturn(Attributes attributes) {
        final String methodName = attributes.getValue(0);
        final String packageName = attributes.getValue(2);
        final String className = attributes.getValue(1);
        SpecificationEntity se = 
                new ReturnValue(methodName,packageName,className);
        tmpMap.put(se, category);
    }

    private void putParam(Attributes attributes) {
        int pos = Integer.parseInt(attributes.getValue(0));
        SpecificationEntity se = 
                new Parameter(pos, attributes.getValue(1),attributes.getValue(3),attributes.getValue(2));
        tmpMap.put(se, category);
    }

    private void putField(Attributes attributes) {
        SpecificationEntity se = 
                new Field(attributes.getValue(0),attributes.getValue(2),attributes.getValue(1));
        tmpMap.put(se, category);
    }

    private void assignCategory(Attributes attributes) {
        categories2domains.put(attributes.getValue(0).intern(), 
                               attributes.getValue(1).intern());
    }

    private void setCategory(Attributes attributes) {
        category = attributes.getValue(0).intern();
    }
    
    private void startSources() {
        tmpMap = sources2categories;
    }
    
    private void startSinks() {
        tmpMap = sinks2categories;
    }
    
    
    /** For debugging purposes. */
    private static String printAttributes (Attributes a) {
        StringBuffer sb = new StringBuffer();
        sb.append('[');
        for (int i= 0; i < a.getLength(); i++) {
            sb.append(a.getValue(i));
            sb.append(';');
        }
        sb.append(']');
        return sb.toString();
    }
    
    static class ErrorHandler implements org.xml.sax.ErrorHandler {
        
        private String getParseExceptionInfo(SAXParseException spe) {
            String systemId = spe.getSystemId();

            if (systemId == null) {
                systemId = "null";
            }

            String info = "URI=" + systemId + " Line=" 
                + spe.getLineNumber() + ": " + spe.getMessage();

            return info;
        }

        @Override
        public void warning(SAXParseException spe) throws SAXException {
            System.out.println("Warning: " + getParseExceptionInfo(spe));
        }
            
        @Override
        public void error(SAXParseException spe) throws SAXException {
            String message = "Error: " + getParseExceptionInfo(spe);
            throw new SAXException(message);
        }

        @Override
        public void fatalError(SAXParseException spe) throws SAXException {
            String message = "Fatal Error: " + getParseExceptionInfo(spe);
            throw new SAXException(message);
        }
        
    }
}
