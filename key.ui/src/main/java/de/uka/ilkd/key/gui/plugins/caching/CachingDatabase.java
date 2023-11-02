/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Queue;
import java.util.Random;
import java.util.Set;
import java.util.regex.Pattern;
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

import org.key_project.util.helper.JsonBuilder;
import org.key_project.util.java.XMLUtil;

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
    private static final Pattern PROOF_HEADER_CLEANER =
        Pattern.compile("(\\\\include|\\\\javaSource) \"[^\"]+\";");

    /**
     * Whether the database is ready for queries.
     */
    private static boolean initDone = false;
    /**
     * Whether the index needs to be written to disk due to changes.
     */
    private static boolean dirty = false;
    /**
     * If true, the database is not in a valid state and may not be saved.
     */
    private static boolean doNotSave = true;
    private static List<CachedProofBranch> cache;
    private static Set<File> cacheProofs;
    private static Map<Integer, CachedFile> files;

    private CachingDatabase() {

    }

    public static void init() {
        if (initDone) {
            return;
        }
        initDone = true;
        cache = new ArrayList<>();
        cacheProofs = new LinkedHashSet<>();
        files = new HashMap<>();

        // read candidates from ~/.key/cachedProofs.xml
        var cacheIndex = PathConfig.getCacheIndex();
        if (!cacheIndex.exists()) {
            doNotSave = false;
            return;
        }

        try {
            var factory = DocumentBuilderFactory.newInstance();
            factory.setFeature("http://xml.org/sax/features/external-general-entities", false);
            factory.setFeature("http://xml.org/sax/features/external-parameter-entities", false);
            var builder = factory.newDocumentBuilder();
            var document = builder.parse(cacheIndex);

            var otherFiles = document.getElementsByTagName("otherFile");
            for (int i = 0; i < otherFiles.getLength(); i++) {
                var entry = otherFiles.item(i);
                var name = entry.getAttributes().getNamedItem("name").getNodeValue();
                var hash = entry.getAttributes().getNamedItem("hash").getNodeValue();
                files.put(Integer.parseInt(hash),
                    new CachedFile(name, Integer.parseInt(hash)));
            }

            var entries = document.getElementsByTagName("entry");
            for (int i = 0; i < entries.getLength(); i++) {
                var entry = entries.item(i);
                var parsed = extractEntry(entry);
                var file = new File(parsed.first);
                var choiceSettings = parsed.second;
                var references = XMLUtil.findElementsByTagName(entry, "referencedFile").stream()
                        .map(x -> {
                            String id = XMLUtil.getAttribute(x, "id");
                            return Objects.requireNonNull(files.get(Integer.parseInt(id)));
                        }).collect(Collectors.toList());
                for (var branch : parsed.third) {
                    cacheProofs.add(file);
                    cache.add(
                        new CachedProofBranch(file, references, choiceSettings, branch.first,
                            branch.second));
                }
            }
            doNotSave = false;
        } catch (Exception e) {
            LOGGER.error("failed to load proof caching database ", e);
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
        save();
        try {
            deleteUnusedFiles();
        } catch (IOException e) {
            LOGGER.error("failed to delete unused files ", e);
        }
    }

    public static void save() {
        init();
        if (!dirty || doNotSave) {
            LOGGER.info("not saving database"); // debug
            return;
        }
        // store cache in ~/.key/cachedProofs.xml
        try {
            var factory = DocumentBuilderFactory.newInstance();
            factory.setFeature("http://xml.org/sax/features/external-general-entities", false);
            factory.setFeature("http://xml.org/sax/features/external-parameter-entities", false);
            var builder = factory.newDocumentBuilder();
            var doc = builder.newDocument();
            var cacheEl = doc.createElement("cacheDatabase");
            doc.appendChild(cacheEl);
            var cachedProofs = doc.createElement("cachedProofs");
            cacheEl.appendChild(cachedProofs);
            var entries = cache.stream().collect(Collectors.groupingBy(w -> w.proofFile));
            for (var entry : entries.values()) {
                var entryEl = doc.createElement("entry");
                cachedProofs.appendChild(entryEl);
                var fileEl = doc.createElement("file");
                fileEl.setTextContent(entry.get(0).proofFile.getAbsolutePath());
                var choiceSettingsEl = doc.createElement("choiceSettings");
                choiceSettingsEl.setTextContent(entry.get(0).choiceSettings);
                entryEl.appendChild(fileEl);
                entryEl.appendChild(choiceSettingsEl);
                var branchesEl = doc.createElement("branches");
                entryEl.appendChild(branchesEl);
                for (var ref : entry.get(0).referencedFiles) {
                    var referencesEl = doc.createElement("referencedFile");
                    referencesEl.setAttribute("id", String.valueOf(ref.hash));
                }

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
            cacheEl.appendChild(cachedFiles);
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

            // new JSON-based store
            JsonBuilder jsonBuilder = null;
            var proofs = jsonBuilder.newArray("proofs");
            int i = 0;
            for (var entry : entries.values()) {
                var proof = proofs.newObject(String.valueOf(i));
                i++;
                proof.putString("file", entry.get(0).proofFile.getAbsolutePath());
                // TODO: ...
            }
            // compilation error to skip tests
            jsonBuilder
        } catch (Exception e) {
            LOGGER.error("failed to save proof cache database ", e);
        }
    }

    /**
     * Delete unused auxiliary files from the cache directory.
     *
     * @throws IOException on error
     */
    private static void deleteUnusedFiles() throws IOException {
        var usedFilenames = new HashSet<>();
        for (var entry : cache) {
            entry.referencedFiles.stream().map(x -> x.filename).forEach(usedFilenames::add);
        }

        var cacheDir = PathConfig.getCacheDirectory();
        var toDelete = new ArrayList<Path>();
        try (var walker = Files.walk(cacheDir.toPath())) {
            walker.forEach(path -> {
                if (Files.isDirectory(path) || usedFilenames.contains(path.getFileName())) {
                    return;
                }
                toDelete.add(path);
            });
        }
        for (Path f : toDelete) {
            Files.delete(f);
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
        if (included != null && included.length() > 0) {
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
        File virtualSrc = null;
        // mirror normal KeY behaviour: read all .java files in the directory
        if (sourceDir != null) {
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
        }
        // TODO: bootstrap path (save hash)
        // TODO: save includes recursively
        // TODO: save proofs compressed

        // construct new header:
        // first, remove old include and javaSource entries
        var proofHeader =
            new StringBuilder(PROOF_HEADER_CLEANER.matcher(proof.header()).replaceAll(""));
        // then add the cached entries
        for (var include : includedNew) {
            proofHeader.append("\\include \"").append(include).append("\";\n");
        }
        if (virtualSrc != null) {
            proofHeader.append("\\javaSource \"").append(virtualSrc).append("\";\n");
        }

        // save to file in ~/.key/cachedProofs/
        File file;
        do {
            var filename = "proof" + (RAND.nextInt(1000000)) + ".proof";
            file = new File(PathConfig.getCacheDirectory(), filename);
        } while (file.exists());
        proof.saveToFileWithHeader(file, proofHeader.toString());

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
        var finalReferences = new ArrayList<CachedFile>();
        finalReferences.addAll(includedNew);
        finalReferences.addAll(sourceNew);
        for (var node : nodesToCheck) {
            cache.add(
                new CachedProofBranch(file, finalReferences, choiceSettings, node.getStepIndex(),
                    node.sequent().toString()));
        }
    }

    public static Collection<CachedProofBranch> findMatching(ChoiceSettings choiceSettings,
            Sequent sequent) {
        init();

        // TODO

        return List.of();
    }

    /**
     * Get a cached file with the specified content. If such a file does not yet
     * exist in the cache directory, a new file will be created.
     *
     * @param content content to look for
     * @param extension file extension
     * @return the cached file
     * @throws IOException if disk access fails
     */
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

    public static Set<File> getAllCachedProofs() {
        init();
        return Collections.unmodifiableSet(cacheProofs);
    }

    public static Map<File, List<CachedProofBranch>> getAllCachedProofBranches() {
        init();
        return cache.stream().collect(Collectors.groupingBy(w -> w.proofFile));
    }

    public static boolean isInUnsafeState() {
        return initDone && !doNotSave;
    }
}
