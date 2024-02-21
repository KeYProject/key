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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.merge.CloseAfterMerge;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.util.KeYConstants;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

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

        // read JSON
        try {
            var document = ParsingFacade.readConfigurationFile(cacheIndex);

            var otherFiles = document.getSection("files");
            for (int i = 0; i < otherFiles.getEntries().size(); i++) {
                var entry = otherFiles.getSection(Integer.toString(i));
                var name = entry.getString("file");
                var hash = entry.getString("hash");
                files.put(Integer.parseInt(hash),
                    new CachedFile(name, Integer.parseInt(hash)));
            }

            var cachedProofsJson = document.getSection("proofs");
            for (int i = 0; i < cachedProofsJson.getEntries().size(); i++) {
                var entry = cachedProofsJson.getSection(Integer.toString(i));
                var file = new File(entry.getString("file"));
                var choiceSettings = entry.getString("choiceSettings");
                var keyVersion = entry.getString("keyVersion");
                var references = entry.getSection("referencedFiles").getEntries().stream()
                        .map(x -> {
                            String id = (String) x.getValue();
                            return Objects.requireNonNull(files.get(Integer.parseInt(id)));
                        }).toList();
                var branches = entry.getSection("cachedSequents");
                for (int j = 0; j < branches.getEntries().size(); j++) {
                    var branch = branches.getSection(Integer.toString(j));
                    var typesFunctions = branch.getSection("typesFunctions");
                    Map<String, String> typesFunctionsMap = new HashMap<>();
                    for (var typeEntry : typesFunctions.getEntries()) {
                        typesFunctionsMap.put(typeEntry.getKey(), (String) typeEntry.getValue());
                    }
                    var typesLocVars = branch.getSection("typesLocVars");
                    Map<String, String> typesLocVarsMap = new HashMap<>();
                    for (var typeEntry : typesLocVars.getEntries()) {
                        typesLocVarsMap.put(typeEntry.getKey(), (String) typeEntry.getValue());
                    }
                    cacheProofs.add(file);
                    cache.add(
                        new CachedProofBranch(file, references, choiceSettings, keyVersion,
                            branch.getInt("stepIndex"),
                            branch.getString("sequent"),
                                typesFunctionsMap,
                                typesLocVarsMap));
                }
            }
            doNotSave = false;
        } catch (Exception e) {
            LOGGER.error("failed to load proof caching database ", e);
        }
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
            LOGGER.info("not saving database");
            return;
        }
        // store cache in ~/.key/cachedProofs.json
        try {
            var docJson = new Configuration();

            var cachedProofsJson = docJson.getOrCreateSection("proofs");
            int i = 0;
            var entries = cache.stream().collect(Collectors.groupingBy(w -> w.proofFile));
            for (var entry : entries.values()) {
                var entryElJson = cachedProofsJson.getOrCreateSection(Integer.toString(i));
                i++;
                entryElJson.set("name", entry.get(0).proofFile.getName());
                entryElJson.set("file", entry.get(0).proofFile.getAbsolutePath());
                entryElJson.set("keyVersion", entry.get(0).keyVersion);
                entryElJson.set("choiceSettings", entry.get(0).choiceSettings);
                var referencedFilesJson = entryElJson.getOrCreateSection("referencedFiles");
                int j = 0;
                for (var ref : entry.get(0).referencedFiles) {
                    referencedFilesJson.set(Integer.toString(j), ref.hash);
                    j++;
                }
                var branchesJson = entryElJson.getOrCreateSection("cachedSequents");
                j = 0;
                for (var branch : entry) {
                    var branchEl = branchesJson.getOrCreateSection(Integer.toString(j));
                    branchEl.set("stepIndex", branch.stepIndex);
                    branchEl.set("sequent", branch.encodeSequent());
                    var functionTypes = branchEl.getOrCreateSection("typesFunctions");
                    branch.getTypesFunctions().forEach(functionTypes::set);
                    var locVarTypes = branchEl.getOrCreateSection("typesLocVars");
                    branch.getTypesLocVars().forEach(locVarTypes::set);
                    j++;
                }
            }
            var cachedFilesJson = docJson.getOrCreateSection("files");
            i = 0;
            for (var entry : files.values()) {
                var entryElJson = cachedFilesJson.getOrCreateSection(Integer.toString(i));
                i++;
                entryElJson.set("file", entry.filename);
                entryElJson.set("hash", Integer.toString(entry.hash));
            }
            // save to file
            var writer = new FileWriter(PathConfig.getCacheIndex());
            docJson.save(writer, "Proof Caching Metadata");
            writer.close();
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
        String choiceSettings = proof.getSettings().getChoiceSettings().toString();
        Queue<Node> nodesToCheck = proof.closedGoals().stream().map(goal -> {
            // first, find the initial node in this branch
            Node n = goal.node();
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
                new CachedProofBranch(file, finalReferences, choiceSettings, KeYConstants.VERSION,
                    node.getStepIndex(),
                    node.sequent(), proof.getServices()));
        }

        // always immediately save database
        save();
    }

    /**
     * Find cache hits for the given sequent.
     *
     * @param choiceSettings choice settings of the current proof
     * @param sequent sequent in current proof
     * @param services services of current proof
     * @return cached proof branches that match the provided sequent
     */
    public static Collection<CachedProofBranch> findMatching(ChoiceSettings choiceSettings,
            Sequent sequent, Services services) {
        init();

        String choiceSettingsString = choiceSettings.toString();

        Set<String> anteFormulas = new HashSet<>();
        sequent.antecedent().forEach(x -> anteFormulas
                .add(LogicPrinter.quickPrintTerm(x.formula(), services, true, false, false)));
        Set<String> succFormulas = new HashSet<>();
        sequent.succedent().forEach(x -> succFormulas
                .add(LogicPrinter.quickPrintTerm(x.formula(), services, true, false, false)));
        List<CachedProofBranch> matching = new ArrayList<>();
        cache.forEach(x -> {
            if (!x.choiceSettings.equals(choiceSettingsString)) {
                return;
            }
            if (x.isCacheHitFor(anteFormulas, succFormulas, sequent)) {
                matching.add(x);
            }
        });

        return matching;
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
