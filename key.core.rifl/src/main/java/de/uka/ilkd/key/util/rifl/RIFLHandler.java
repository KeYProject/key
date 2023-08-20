/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.rifl;

import java.util.*;
import java.util.Map.Entry;

import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.KeYCollections;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;
import org.xml.sax.helpers.DefaultHandler;

import static de.uka.ilkd.key.util.rifl.SpecificationEntity.*;

/**
 * XML content handler for the RIFL language. Produces a RIFL {@link SpecificationContainer}. May
 * throw obscure exceptions on non-wellformed XML documents. Refer to the RIFL 1.0 Language
 * definition by Ereth, Mantel, and Perner.
 *
 * @author bruns
 */
class RIFLHandler extends DefaultHandler {
    private static final Logger LOGGER = LoggerFactory.getLogger(RIFLHandler.class);

    static class ErrorHandler implements org.xml.sax.ErrorHandler {



        @Override
        public void error(SAXParseException spe) throws SAXException {
            final String message = "Error: " + getParseExceptionInfo(spe);
            throw new SAXException(message);
        }

        @Override
        public void fatalError(SAXParseException spe) throws SAXException {
            final String message = "Fatal Error: " + getParseExceptionInfo(spe);
            throw new SAXException(message);
        }

        private String getParseExceptionInfo(SAXParseException spe) {
            String systemId = spe.getSystemId();
            if (systemId == null) {
                systemId = "null";
            }
            return "URI=" + systemId + " Line=" + spe.getLineNumber() + ": " + spe.getMessage();
        }

        @Override
        public void warning(SAXParseException spe) throws SAXException {
            LOGGER.warn("Warning: {}", getParseExceptionInfo(spe));
        }
    }

    private static final String DEFAULT_CATEGORY = "Spider Pig";
    private static final String DEFAULT_DOMAIN = "low";

    /** For debugging purposes. */
    @SuppressWarnings("unused")
    private static String printAttributes(Attributes a) {
        final var sb = new StringBuilder();
        sb.append('[');
        for (int i = 0; i < a.getLength(); i++) {
            sb.append(a.getValue(i));
            sb.append(';');
        }
        sb.append(']');
        return sb.toString();
    }

    private final Map<SpecificationEntity, Pair<String, String>> sources2categories =
        new LinkedHashMap<>();
    private final Map<SpecificationEntity, Pair<String, String>> sinks2categories =
        new LinkedHashMap<>();
    private final Map<Pair<String, String>, String> categories2domains = new LinkedHashMap<>();
    private final Map<String, String> handles2categories = new LinkedHashMap<>();
    private Set<String> domains = new LinkedHashSet<>();
    private Set<Entry<String, String>> flow = new LinkedHashSet<>();
    private Map<SpecificationEntity, Pair<String, String>> tmpMap = null;
    private Type type = null;

    private String tmpHandle = null;

    private String category = DEFAULT_CATEGORY;


    public RIFLHandler() {
    }

    private void assignHandle(Attributes attributes) {
        final String handle = attributes.getValue("handle").intern();
        final String domain = attributes.getValue("domain").intern();
        Pair<String, String> p = new Pair<>(handle, handles2categories.get(handle));
        categories2domains.put(p, domain);
    }

    private void setAssignable(Attributes attributes) {
        assert tmpHandle == null;
        tmpHandle = attributes.getValue("handle");
    }

    private void unsetAssignable() {
        assert tmpHandle != null;
        tmpHandle = null;
    }

    @Override
    public void endDocument() {
        // TODO: consistency validation
    }

    public SpecificationContainer getSpecification() {
        // drop categories, merge sources and sinks
        final Map<SpecificationEntity, String> tmp = new LinkedHashMap<>();
        tmp.putAll(KeYCollections.apply(sources2categories, categories2domains));
        tmp.putAll(KeYCollections.apply(sinks2categories, categories2domains));
        return new DefaultSpecificationContainer(tmp, flow);
    }

    private void putField(Attributes attributes) {
        final String field = attributes.getValue("name");
        final String clazz = attributes.getValue("class");
        final String packg = attributes.getValue("package");
        final SpecificationEntity se = new Field(field, packg, clazz, type);
        handles2categories.put(tmpHandle, category);
        tmpMap.put(se, new Pair<>(tmpHandle, category));
    }

    private void putParam(Attributes attributes) {
        final String packg = attributes.getValue("package");
        final String clazz = attributes.getValue("class");
        final String method = attributes.getValue("method");
        final int param = Integer.parseInt(attributes.getValue("parameter"));
        final SpecificationEntity se = new Parameter(param, method, packg, clazz, type);
        handles2categories.put(tmpHandle, category);
        tmpMap.put(se, new Pair<>(tmpHandle, category));
    }

    private void putReturn(Attributes attributes) {
        final String packageName = attributes.getValue("package");
        final String className = attributes.getValue("class");
        final String methodName = attributes.getValue("method");
        final SpecificationEntity se = new ReturnValue(methodName, packageName, className, type);
        handles2categories.put(tmpHandle, category);
        tmpMap.put(se, new Pair<>(tmpHandle, category));
    }

    private void putFlow(Attributes attributes) {
        final String from = attributes.getValue("from");
        final String to = attributes.getValue("to");
        assert !from.equals(to);
        final Entry<String, String> e = new AbstractMap.SimpleEntry<>(from, to);
        flow.add(e);
    }

    private void putDomain(Attributes attributes) {
        final String domainName = attributes.getValue("name");
        domains.add(domainName);
    }

    private void setCategory(Attributes attributes) {
        assert Objects.equals(category, DEFAULT_CATEGORY);
        category = attributes.getValue("name").intern();
    }

    private void unsetCategory() {
        assert !Objects.equals(category, DEFAULT_CATEGORY);
        category = DEFAULT_CATEGORY;
    }

    private void checkDomains() {
        assert !domains.isEmpty();
        assert domains.contains(DEFAULT_DOMAIN);
    }

    private void checkDomainAssignmentsWithFlows() {
        // This method tried to remove flows implicitly assumed by JML,
        // but for more than two domains this would need a default "high domain".

        /*
         * final Iterator<Pair<String,String>> it = categories2domains.keySet().iterator(); for
         * (Pair<String,String> p = it.next(); it.hasNext(); p = it.next()) {
         * for(Entry<String,String> e : flow){ if(e.getKey().equals(DEFAULT_DOMAIN) &&
         * categories2domains.containsKey(p) && categories2domains.get(p).equals(e.getValue())){ if
         * (p.first.equals("h")) { throw new RuntimeException(); } it.remove(); } }
         *
         * }
         */
    }

    private void checkFlows() {
        for (var p : categories2domains.entrySet()) {
            assert domains.contains(categories2domains.get(p.getKey()));
        }
    }

    @Override
    public void startElement(String uri, String localName, String qName, Attributes attributes) {

        switch (localName) {
        case "sourcedompair":
        case "source":
            startSources();
            break;
        case "sinkdompair":
        case "sink":
            startSinks();
            break;
        case "category": // TODO: different semantics in "domains" and "sinkdompair"
            setCategory(attributes);
            break;
        case "assign":
            assignHandle(attributes);
            break;
        // case "domainassignment":
        case "domains":
            startDomains();
            break;
        case "domain":
            putDomain(attributes);
            break;
        case "assignable":
            setAssignable(attributes);
            break;
        case "field":
            putField(attributes);
            break;
        case "parameter":
            putParam(attributes);
            break;
        case "returnvalue":
            putReturn(attributes);
            break;
        case "flowrelation":
            startFlow();
            break;
        case "flow":
            putFlow(attributes);
            break;
        // a lot of elements without their own semantics
        // case "riflspec":
        // case "attackerio":
        // case "top":
        // case "bottom":
        // case "source":
        // case "sink":
        case "dompair": // TODO
            // case "domainhierarchy":
        case "flowpair": // TODO
            // case "flowpolicy":
        default:
        }
    }

    @Override
    public void endElement(String uri, String localName, String qName) {
        switch (localName) {
        case "assignable":
            unsetAssignable();
            break;
        case "category":
            unsetCategory();
            break;
        case "domains":
            checkDomains();
            break;
        case "domainassignment":
            checkDomainAssignmentsWithFlows();
            break;
        case "flowrelation":
            checkFlows();
            break;
        default:
        }
    }

    // TODO: actions on closing elements?

    private void startDomains() {
        domains = new LinkedHashSet<>();
    }

    private void startFlow() {
        flow = new LinkedHashSet<>();
    }

    private void startSinks() {
        tmpMap = sinks2categories;
        type = Type.SINK;
    }

    private void startSources() {
        tmpMap = sources2categories;
        type = Type.SOURCE;
    }
}
