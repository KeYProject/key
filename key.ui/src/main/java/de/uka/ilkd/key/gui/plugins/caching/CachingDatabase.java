package de.uka.ilkd.key.gui.plugins.caching;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Queue;
import java.util.Random;
import java.util.stream.Collectors;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.merge.CloseAfterMerge;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.w3c.dom.Node;

/**
 * Database of externally saved proofs to use in caching.
 *
 * @author Arne Keller
 */
public final class CachingDatabase {

    private static final Logger LOGGER = LoggerFactory.getLogger(CachingDatabase.class);
    private static final Random RAND = new Random();
    private static final PathMatcher JAVA_MATCHER =
        FileSystems.getDefault().getPathMatcher("glob:*.java");

    private static boolean initDone = false;
    private static boolean dirty = false;
    private static List<CachedProofBranch> cache;
    private static Map<Integer, CachedFile> files;

    private CachingDatabase() {

    }

    public static void init() {
        if (initDone) {
            return;
        }
        initDone = true;
        cache = new ArrayList<>();
        files = new HashMap<>();

        // read candidates from ~/.key/cachedProofs.xml
        var cacheIndex = PathConfig.getCacheIndex();
        if (!cacheIndex.exists()) {
            return;
        }

        try {
            var factory = DocumentBuilderFactory.newInstance();
            factory.setFeature("http://xml.org/sax/features/external-general-entities", false);
            factory.setFeature("http://xml.org/sax/features/external-parameter-entities", false);
            var builder = factory.newDocumentBuilder();
            var document = builder.parse(cacheIndex);
            var entries = document.getElementsByTagName("entry");
            for (int i = 0; i < entries.getLength(); i++) {
                var entry = entries.item(i);
                var parsed = extractEntry(entry);
                var file = new File(parsed.first);
                var choiceSettings = parsed.second;
                for (var branch : parsed.third) {
                    cache.add(
                        new CachedProofBranch(file, choiceSettings, branch.first, branch.second));
                }
            }
            var files = document.getElementsByTagName("otherFile");
            for (int i = 0; i < files.getLength(); i++) {
                var entry = files.item(i);
                var name = entry.getAttributes().getNamedItem("name").getNodeValue();
                var hash = entry.getAttributes().getNamedItem("hash").getNodeValue();
                CachingDatabase.files.put(Integer.parseInt(hash),
                    new CachedFile(name, Integer.parseInt(hash)));
            }
        } catch (Exception e) {
            LOGGER.error("failed to load proof caching database ", e);
            // TODO: add a safeguard to not delete the index file on the next write
        }
    }

    private static Triple<String, String, List<Pair<Integer, String>>> extractEntry(Node entry) {
        String file = null;
        String choiceSettings = null;
        List<Pair<Integer, String>> branches = new ArrayList<>();
        var childNodes = entry.getChildNodes();
        for (int i = 0; i < childNodes.getLength(); i++) {
            var childNode = childNodes.item(i);
            if (childNode.getNodeName().equals("file")) {
                file = childNode.getTextContent();
            } else if (childNode.getNodeName().equals("choiceSettings")) {
                choiceSettings = childNode.getTextContent();
            } else if (childNode.getNodeName().equals("branches")) {
                var branchNodes = childNode.getChildNodes();
                for (int j = 0; j < branchNodes.getLength(); j++) {
                    String sequent = "";
                    int stepIndex = -1;
                    var branchData = branchNodes.item(j).getChildNodes();
                    for (int k = 0; k < branchData.getLength(); k++) {
                        var data = branchData.item(k);
                        if (data.getNodeName().equals("sequent")) {
                            sequent = data.getTextContent();
                        } else if (data.getNodeName().equals("stepIndex")) {
                            stepIndex = Integer.parseInt(data.getTextContent());
                        }
                    }
                    branches.add(new Pair<>(stepIndex, sequent));
                }
            }
        }
        return new Triple<>(file, choiceSettings, branches);
    }

    /**
     * Shut the caching database down. Writes the index to disk if changes have been done.
     */
    public static void shutdown() {
        if (!dirty) {
            return;
        }
        // store cache in ~/.key/cachedProofs.xml
        try {
            var factory = DocumentBuilderFactory.newInstance();
            factory.setFeature("http://xml.org/sax/features/external-general-entities", false);
            factory.setFeature("http://xml.org/sax/features/external-parameter-entities", false);
            var builder = factory.newDocumentBuilder();
            var doc = builder.newDocument();
            var cachedProofs = doc.createElement("cachedProofs");
            doc.appendChild(cachedProofs);
            var entries = cache.stream().collect(Collectors.groupingBy(w -> w.proofFile));
            for (var entry : entries.values()) {
                var entryEl = doc.createElement("entry");
                cachedProofs.appendChild(entryEl);
                var fileEl = doc.createElement("file");
                fileEl.setTextContent(entry.get(0).proofFile.getAbsolutePath());
                var choiceSettingsEl = doc.createElement("choiceSettings");
                fileEl.setTextContent(entry.get(0).choiceSettings);
                entryEl.appendChild(fileEl);
                entryEl.appendChild(choiceSettingsEl);
                var branchesEl = doc.createElement("branches");
                entryEl.appendChild(branchesEl);

                for (var branch : entry) {
                    var branchEl = doc.createElement("branch");
                    branchesEl.appendChild(branchEl);
                    var sequentEl = doc.createElement("sequent");
                    sequentEl.setTextContent(branch.sequent);
                    branchEl.appendChild(sequentEl);
                    var stepIndexEl = doc.createElement("stepIndex");
                    stepIndexEl.setTextContent(String.valueOf(branch.stepIndex));
                    branchEl.appendChild(stepIndexEl);
                }
            }
            var cachedFiles = doc.createElement("cachedFiles");
            doc.appendChild(cachedFiles);
            for (var entry : files.values()) {
                var entryEl = doc.createElement("otherFile");
                entryEl.setAttribute("name", entry.filename);
                entryEl.setAttribute("hash", Integer.toString(entry.hash));
                cachedFiles.appendChild(entryEl);
            }
            // save to file
            var transformerFactory = TransformerFactory.newInstance();
            var transformer = transformerFactory.newTransformer();
            var source = new DOMSource(doc);
            var writer = new FileWriter(PathConfig.getCacheIndex());
            var result = new StreamResult(writer);
            transformer.transform(source, result);
        } catch (Exception e) {
            LOGGER.error("failed to save proof cache database ", e);
        }
    }

    /**
     * Add a new proof to the database. Automatically saves a copy of the proof.
     * This will also copy associated files (includes, java source files, ...) into the
     * cache database.
     *
     * @param proof the proof to store
     */
    public static void addProof(Proof proof) throws IOException {
        init();
        dirty = true;
        PathConfig.getCacheDirectory().mkdirs();

        // save included (or otherwise referenced files) in ~/.key/cachedProofs/
        var included = proof.getServices().getJavaModel().getIncludedFiles();
        List<CachedFile> includedNew = new ArrayList<>();
        if (included.length() > 0) {
            for (var include : included.split(", ")) {
                var absPath = include.substring(1, include.length() - 1);
                // load into memory
                var content = Files.readString(Path.of(absPath));
                includedNew.add(getCached(content, "key"));
            }
        }
        // save Java source files in ~/.key/cachedProofs/
        var sourceDir = proof.getServices().getJavaModel().getModelDir();
        List<CachedFile> sourceNew = new ArrayList<>();
        // mirror normal KeY behaviour: read all .java files in the directory
        try (var walker = Files.walk(Path.of(sourceDir))) {
            walker.forEach(path -> {
                if (!JAVA_MATCHER.matches(path.getFileName())) {
                    return;
                }
                try {
                    var content = Files.readString(path);
                    sourceNew.add(CachingDatabase.getCached(content, "java"));
                } catch (IOException e) {
                    LOGGER.error("failed to save java source ", e);
                }
            });
        }
        // create a simulated source directory
        File virtualSrc;
        do {
            var filename = "javaSource" + (RAND.nextInt(1000000));
            virtualSrc = new File(PathConfig.getCacheDirectory(), filename);
        } while (virtualSrc.exists());
        virtualSrc.mkdir();
        var virtualSource = Path.of(virtualSrc.toURI());
        for (var path : sourceNew) {
            Files.createLink(virtualSource.resolve(path.filename),
                PathConfig.getCacheDirectory().toPath().resolve(path.filename));
        }
        // TODO: bootstrap path (save hash)
        // TODO: modify existing proof header
        // TODO: save includes recursively
        // TODO: save proofs compressed

        // construct new header
        var proofHeader = new StringBuilder();
        for (var include : includedNew) {
            proofHeader.append("\\include \"").append(include).append("\";\n");
        }
        proofHeader.append("\\javaSource \"").append(virtualSrc).append("\";\n");
        var oldHeader = proof.header();
        proof.setProblemHeader(proofHeader.toString());

        // save to file in ~/.key/cachedProofs/
        File file;
        do {
            var filename = "proof" + (RAND.nextInt(1000000)) + ".proof";
            file = new File(PathConfig.getCacheDirectory(), filename);
        } while (file.exists());
        proof.saveToFile(file);

        proof.setProblemHeader(oldHeader);

        // save sequents of candidate nodes in cache
        proof.setStepIndices();
        // only search in compatible proofs
        String choiceSettings = proof.getSettings().getChoiceSettings().toString();
        Queue<de.uka.ilkd.key.proof.Node> nodesToCheck = proof.closedGoals().stream().map(goal -> {
            // first, find the initial node in this branch
            de.uka.ilkd.key.proof.Node n = goal.node();
            if (n.parent() != null
                    && n.parent().getAppliedRuleApp().rule() == CloseAfterMerge.INSTANCE) {
                // cannot reference this kind of branch
                return null;
            }
            // find first node in branch
            while (n.parent() != null && n.parent().childrenCount() == 1) {
                n = n.parent();
            }
            return n;
        }).filter(Objects::nonNull).collect(Collectors.toCollection(ArrayDeque::new));
        for (var node : nodesToCheck) {
            cache.add(new CachedProofBranch(file, choiceSettings, node.getStepIndex(),
                node.sequent().toString()));
        }
    }

    public static Collection<CachedProofBranch> findMatching(ChoiceSettings choiceSettings,
            Sequent sequent) {
        init();

        return List.of();
    }

    private static CachedFile getCached(String content, String extension) throws IOException {
        int hash = content.hashCode();
        if (files.containsKey(hash)) {
            return files.get(hash);
        }
        File file;
        do {
            var filename = extension + (RAND.nextInt(1000000)) + "." + extension;
            file = new File(PathConfig.getCacheDirectory(), filename);
        } while (file.exists());
        Files.write(Path.of(file.toURI()), content.getBytes(StandardCharsets.UTF_8));
        var cachedFile = new CachedFile(file.getName(), hash);
        files.put(hash, cachedFile);
        return cachedFile;
    }
}
