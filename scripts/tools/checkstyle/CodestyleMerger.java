package org.key_project.codestylemerger;

import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.io.File;
import java.io.IOException;
import java.util.TreeMap;

/**
 * Small utility to merge two code style files of the Eclipse formatter (as produced by the IDE when
 * exporting code styles) into a single one. All entries with keys that are only present in one of
 * them will end up in the output. When the option "--overwriteValues" is set, then entries that are
 * present in both input files are taken from the new file, otherwise they are taken from the old
 * one.
 * <br>
 * The entries in the output are sorted lexicographically by the key names.
 *
 * @author Wolfram Pfeifer
 */
public class CodestyleMerger {

    // TODO: for an easier implementation, the flag overwriteValues can only be used at the end ...
    public static final String USAGE = "Usage: codestylemerger <oldFile> <newFile> <outputFile> [--overwriteValues]";
    public static final boolean VERBOSE = false; // could be an additional option in the future,

    public static void main(String[] args) {

        if (args.length < 3 || args.length > 4) {
            System.out.println(USAGE);
            System.exit(-1);
        }

        boolean overwriteValues = false;
        if (args.length == 4) {
            String option = args[3];
            if (option.equals("--overwriteValues")) {
                overwriteValues = true;
            } else {
                System.out.println(USAGE);
                System.exit(-1);
            }
        }

        final File key = new File(args[0]);
        final File other = new File(args[1]);
        final File output = new File(args[2]);

        try {
            DocumentBuilder builder = DocumentBuilderFactory.newInstance().newDocumentBuilder();

            Document origDoc = builder.parse(key);
            origDoc.getDocumentElement().normalize();
            Document newDoc = builder.parse(other);
            newDoc.getDocumentElement().normalize();

            // 1) read all entries of old and new file (using TreeMaps to keep entries sorted)
            TreeMap<String, Node> oldEntries = readXMLEntries(origDoc);
            TreeMap<String, Node> newEntries = readXMLEntries(newDoc);

            // log entries that are only present in the old file
            oldEntries.forEach((k, v) -> { if (newEntries.get(k) == null) {
                if (VERBOSE) {
                    System.out.println("Only present in old file: " + k);
                }
            }});

            // 3) merge the entries
            TreeMap<String, Node> resultEntries = mergeXMLEntries(oldEntries, newEntries,
                overwriteValues);

            // 4) clear the existing profile
            Node profile = origDoc.getElementsByTagName("profile").item(0);
            while (profile.hasChildNodes()) {
                profile.removeChild(profile.getFirstChild());
            }

            // 5) write the new profile
            resultEntries.forEach((s, n) -> {
                Node cloneNode = origDoc.adoptNode(n);
                profile.appendChild(cloneNode);
            });

            // this seems to be the easiest way to get nice formatting ...
            trimWhitespace(origDoc);

            // make sure that a proper indentation is used:
            Transformer transformer = TransformerFactory.newInstance().newTransformer();
            transformer.setOutputProperty(OutputKeys.INDENT, "yes");
            transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "4");

            DOMSource dom = new DOMSource(origDoc);
            StreamResult result = new StreamResult(output);
            transformer.transform(dom, result);

            // output to console for debugging
            //StreamResult res = new StreamResult(System.out);
            //transformer.transform(dom, res);
            System.out.println("Successfully wrote to file " + args[2]);
        } catch (ParserConfigurationException | TransformerException | IOException | SAXException e) {
            System.out.println(USAGE);
            throw new RuntimeException(e);
        }
    }

    private static TreeMap<String, Node> mergeXMLEntries(TreeMap<String, Node> oldEntries,
                                                         TreeMap<String, Node> newEntries,
                                                         boolean overwriteValues) {
        TreeMap<String, Node> resultEntries = new TreeMap<>(oldEntries);
        newEntries.forEach((k, v) -> {
            if (!resultEntries.containsKey(k)) {
                resultEntries.put(k, v);
                if (VERBOSE) {
                    System.out.println("Only present in new file: " + k);
                }
            } else if (resultEntries.containsKey(k) && overwriteValues) {
                resultEntries.put(k, v);
                if (VERBOSE) {
                    System.out.println("Replacing key " + k);
                }
            } else {
                // maybe with a future verbosity level
                if (VERBOSE) {
                    //System.out.println("Ignoring key " + k);
                }
            }
        });
        return resultEntries;
    }

    private static TreeMap<String, Node> readXMLEntries(Document origDoc) {
        TreeMap<String, Node> entries = new TreeMap<>();
        NodeList ls = origDoc.getElementsByTagName("setting");
        for (int i = 0; i < ls.getLength(); i++) {
            Node n = ls.item(i);
            String k = n.getAttributes().getNamedItem("id").getNodeValue();
            entries.put(k, n);
        }
        return entries;
    }

    private static void trimWhitespace(Node node) {
        NodeList children = node.getChildNodes();
        for(int i = 0; i < children.getLength(); ++i) {
            Node child = children.item(i);
            if(child.getNodeType() == Node.TEXT_NODE) {
                child.setTextContent(child.getTextContent().trim());
            }
            trimWhitespace(child);
        }
    }
}