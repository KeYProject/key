/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching.database;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
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
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Queue;
import java.util.Random;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import de.uka.ilkd.key.gui.plugins.caching.CachedFile;
import de.uka.ilkd.key.gui.plugins.caching.CachedProofBranch;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ReferenceSearcher;
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
    /**
     * RNG for filenames in the proof/auxiliary files store.
     */
    private static final Random RAND = new Random();
    /**
     * Matcher to match .java files.
     */
    private static final PathMatcher JAVA_MATCHER =
        FileSystems.getDefault().getPathMatcher("glob:*.java");
    /**
     * Regex to capture include or javaSource directives in the proof.
     */
    private static final Pattern PROOF_HEADER_CLEANER =
        Pattern.compile("(\\\\include|\\\\javaSource) \"[^\"]+\";");

    /**
     * Path to metadata file.
     */
    private final Path metadataIndex;
    /**
     * Path to storage directory for proof/java/key files.
     */
    private final Path cacheIndex;
    /**
     * Whether the index needs to be written to disk due to changes.
     */
    private boolean dirty = false;
    /**
     * The proof branches available in this cache, sorted by the file they are stored in.
     */
    private Map<Path, List<CachedProofBranch>> cache;
    /**
     * The auxiliary files available in this cache.
     * Keyed based on the {@link String#hashCode()} of their contents.
     */
    private Map<Integer, CachedFile> files;

    /**
     * Create a new caching database by reading the provided metadata index.
     *
     * @param metadataIndex path to metadata index
     * @param cacheIndex path to storage directory for auxiliary files
     */
    public CachingDatabase(Path metadataIndex, Path cacheIndex) {
        this.metadataIndex = metadataIndex;
        this.cacheIndex = cacheIndex;
        init();
    }

    /**
     * Reset the database. Removes all cached proofs.
     *
     * @throws IOException if there is an error deleting the files
     */
    public void reset() throws IOException {
        cache = new HashMap<>();
        files = new HashMap<>();
        dirty = true;
        save();
        deleteUnusedFiles();
    }

    /**
     * Initialize the database.
     * This will read the previously saved metadata from disk.
     */
    private void init() {
        cache = new HashMap<>();
        files = new HashMap<>();

        // read candidates from ~/.key/cachedProofs.json
        if (!metadataIndex.toFile().exists()) {
            return;
        }

        // read JSON
        try {
            var document = ParsingFacade.readConfigurationFile(metadataIndex);

            var otherFiles = document.getSection("files");
            for (int i = 0; i < otherFiles.getEntries().size(); i++) {
                var entry = otherFiles.getSection(Integer.toString(i));
                var name = entry.getString("file");
                var hash = entry.getInt("hash");
                files.put(hash,
                    new CachedFile(new File(name).toPath(), hash));
            }

            var cachedProofsJson = document.getSection("proofs");
            for (int i = 0; i < cachedProofsJson.getEntries().size(); i++) {
                var entry = cachedProofsJson.getSection(Integer.toString(i));
                var file = Path.of(entry.getString("file"));
                var name = entry.getString("name");
                var choiceSettings = entry.getString("choiceSettings");
                var keyVersion = entry.getString("keyVersion");
                var javaClasses = entry.getStringList("javaClasses");
                var references = entry.getSection("referencedFiles").getEntries().stream()
                        .map(x -> {
                            Long id = (Long) x.getValue();
                            return files.get(id.intValue());
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
                    var ante = branch.getStringList("sequentAnte");
                    var succ = branch.getStringList("sequentSucc");

                    if (!cache.containsKey(file)) {
                        cache.put(file, new ArrayList<>());
                    }
                    cache.get(file).add(
                        new CachedProofBranch(file, name, references, choiceSettings, keyVersion,
                            branch.getInt("stepIndex"),
                            ante, succ,
                            typesFunctionsMap,
                            typesLocVarsMap,
                            javaClasses));
                }
            }
        } catch (Exception e) {
            LOGGER.error("failed to load proof caching database ", e);
        }
    }

    /**
     * Shut the caching database down. Writes the index to disk if changes have been done.
     */
    public void shutdown() {
        save();
        try {
            deleteUnusedFiles();
        } catch (IOException e) {
            LOGGER.error("failed to delete unused files ", e);
        }
    }

    public void save() {
        if (!dirty) {
            LOGGER.info("not saving database (not dirty)");
            return;
        }
        // store cache in ~/.key/cachedProofs.json
        try {
            var docJson = new Configuration();

            var cachedProofsJson = docJson.getOrCreateSection("proofs");
            int i = 0;
            for (var entry : cache.values()) {
                var entryElJson = cachedProofsJson.getOrCreateSection(Integer.toString(i));
                i++;
                entryElJson.set("name", entry.get(0).proofName);
                entryElJson.set("file", entry.get(0).proofFile.toAbsolutePath().toString());
                entryElJson.set("keyVersion", entry.get(0).keyVersion);
                entryElJson.set("choiceSettings", entry.get(0).choiceSettings);
                entryElJson.set("javaClasses", entry.get(0).getJavaClasses());
                var referencedFilesJson = entryElJson.getOrCreateSection("referencedFiles");
                int j = 0;
                for (var ref : entry.get(0).getReferencedFiles()) {
                    referencedFilesJson.set(Integer.toString(j), ref.hash());
                    j++;
                }
                var branchesJson = entryElJson.getOrCreateSection("cachedSequents");
                j = 0;
                for (var branch : entry) {
                    var branchEl = branchesJson.getOrCreateSection(Integer.toString(j));
                    branchEl.set("stepIndex", branch.stepIndex);
                    branchEl.set("sequentAnte", branch.getSequentAnte());
                    branchEl.set("sequentSucc", branch.getSequentSucc());
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
                entryElJson.set("file", entry.file().toAbsolutePath().toString());
                entryElJson.set("hash", entry.hash());
            }
            // save to file
            var writer = new FileWriter(metadataIndex.toFile());
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
    private void deleteUnusedFiles() throws IOException {
        Set<String> usedFilenames = new HashSet<>();
        for (var cacheFile : cache.values()) {
            for (var entry : cacheFile) {
                usedFilenames.add(entry.proofFile.getFileName().toString());
                entry.getReferencedFiles().stream().map(x -> x.file().getFileName().toString())
                        .forEach(usedFilenames::add);
            }
        }

        var cacheDir = PathConfig.getCacheDirectory();
        var toDelete = new ArrayList<Path>();
        try (var walker = Files.walk(cacheDir)) {
            walker.forEach(path -> {
                if (Files.isDirectory(path)
                        || usedFilenames.contains(path.getFileName().toString())) {
                    return;
                }
                toDelete.add(path);
            });
        }
        for (Path f : toDelete) {
            LOGGER.info("deleting unused file {}", f);
            Files.delete(f);
        }
        toDelete.clear();
        // second pass: delete empty directories
        try (var walker = Files.walk(cacheDir)) {
            walker.forEach(path -> {
                try {
                    if (Files.isDirectory(path) && !path.equals(cacheDir)) {
                        try (var childrenFiles = Files.list(path)) {
                            if (childrenFiles.findFirst().isEmpty()) {
                                toDelete.add(path);
                            }
                        }
                    }
                } catch (IOException e) {
                    // ignore read I/O errors
                }
            });
        }
        for (Path f : toDelete) {
            LOGGER.info("deleting empty directory {}", f);
            Files.delete(f);
        }
    }

    /**
     * Add a new proof to the database. Automatically saves a copy of the proof.
     * This will also copy associated files (includes, java source files, ...) into the
     * cache database.
     *
     * @param proof the proof to store
     * @throws IOException if there is an I/O error saving the proof
     */
    public void addProof(Proof proof) throws IOException {
        dirty = true;
        cacheIndex.toFile().mkdirs();

        // save included (or otherwise referenced files) in ~/.key/cachedProofs/
        var included = proof.getServices().getJavaModel().getIncludedFiles();
        List<CachedFile> includedNew = new ArrayList<>();
        if (included != null && !included.isEmpty()) {
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
        List<String> referencedClasses = new ArrayList<>();
        Path virtualSrc = null;
        // mirror normal KeY behaviour: read all .java files in the directory
        if (sourceDir != null) {
            try (var walker = Files.walk(Path.of(sourceDir))) {
                walker.forEach(path -> {
                    if (!JAVA_MATCHER.matches(path.getFileName())) {
                        return;
                    }
                    try {
                        var content = Files.readString(path);
                        referencedClasses.add(path.getFileName().toString());
                        sourceNew.add(getCached(content, "java"));
                    } catch (IOException e) {
                        LOGGER.error("failed to save java source ", e);
                    }
                });
            }
            // create a simulated source directory
            do {
                var filename = "javaSource" + (RAND.nextInt(1000000));
                virtualSrc = cacheIndex.resolve(filename);
            } while (virtualSrc.toFile().exists());
            virtualSrc.toFile().mkdir();
            for (var path : sourceNew) {
                Files.createLink(virtualSrc.resolve(path.file().getFileName().toString()),
                    path.file());
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
        Path file;
        do {
            var filename = "proof" + (RAND.nextInt(1000000)) + ".proof";
            file = cacheIndex.resolve(filename);
        } while (file.toFile().exists());
        proof.saveToFileWithHeader(file.toFile(), proofHeader.toString());

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
        // expand candidate nodes to higher branches
        // seenLastNodes: which last nodes of branches have already been checked
        Set<Node> seenLastNodes = new HashSet<>();
        // lastNodesToCheck: which last nodes of branches should be traversed upwards
        List<Node> lastNodesToCheck = new ArrayList<>();
        nodesToCheck.forEach(x -> {
            var parent = x.parent();
            if (parent != null) {
                lastNodesToCheck.add(parent);
            }
        });
        while (!lastNodesToCheck.isEmpty()) {
            Node toCheck = lastNodesToCheck.remove(lastNodesToCheck.size() - 1);
            if (seenLastNodes.contains(toCheck)) {
                continue;
            }
            seenLastNodes.add(toCheck);
            while (toCheck.parent() != null && toCheck.parent().childrenCount() == 1) {
                toCheck = toCheck.parent();
            }
            // check whether this node is even suitable for close by reference first
            if (ReferenceSearcher.suitableForCloseByReference(toCheck)) {
                nodesToCheck.add(toCheck);
                if (toCheck.parent() != null) {
                    lastNodesToCheck.add(toCheck.parent());
                }
            }
        }

        var finalReferences = new ArrayList<CachedFile>();
        finalReferences.addAll(includedNew);
        finalReferences.addAll(sourceNew);
        List<CachedProofBranch> cacheEntries = new ArrayList<>();
        for (var node : nodesToCheck) {
            cacheEntries.add(
                new CachedProofBranch(file, proof.name().toString(), finalReferences,
                    choiceSettings,
                    KeYConstants.VERSION, node.getStepIndex(), node.sequent(),
                    proof.getServices(), referencedClasses));
        }
        cache.put(file.toAbsolutePath(), cacheEntries);

        // always immediately save database
        save();
    }

    /**
     * Remove a proof from this database.
     *
     * @param pathToProof the (absolute) path to the proof
     */
    public void removeProof(Path pathToProof) throws IOException {
        cache.remove(pathToProof);
        Files.delete(pathToProof);
        dirty = true;
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
    public Collection<CachedProofBranch> findMatching(ChoiceSettings choiceSettings,
            Sequent sequent, Services services) {
        String choiceSettingsString = choiceSettings.toString();

        Set<String> anteFormulas = new HashSet<>();
        sequent.antecedent().forEach(x -> anteFormulas
                .add(LogicPrinter.quickPrintTerm(x.formula(), services, true, false, false)));
        Set<String> succFormulas = new HashSet<>();
        sequent.succedent().forEach(x -> succFormulas
                .add(LogicPrinter.quickPrintTerm(x.formula(), services, true, false, false)));
        List<CachedProofBranch> matching = new ArrayList<>();
        cache.values().forEach(x -> {
            for (var cacheBranch : x) {
                if (!cacheBranch.choiceSettings.equals(choiceSettingsString)) {
                    return;
                }
                if (!cacheBranch.keyVersion.equals(KeYConstants.VERSION)) {
                    return;
                }
                if (cacheBranch.isCacheHitFor(anteFormulas, succFormulas, sequent)) {
                    matching.add(cacheBranch);
                }
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
    private CachedFile getCached(String content, String extension) throws IOException {
        int hash = content.hashCode();
        if (files.containsKey(hash)) {
            return files.get(hash);
        }
        Path file;
        do {
            var filename = extension + (RAND.nextInt(1000000)) + "." + extension;
            file = cacheIndex.resolve(filename);
        } while (file.toFile().exists());
        LOGGER.info("creating new file {}", file);
        Files.writeString(file, content);
        var cachedFile = new CachedFile(file, hash);
        files.put(hash, cachedFile);
        return cachedFile;
    }

    public Set<Path> getAllCachedProofs() {
        return cache.keySet();
    }

    public Map<Path, List<CachedProofBranch>> getAllCachedProofBranches() {
        return Collections.unmodifiableMap(cache);
    }

    /**
     * @return the size of the metadata file
     * @throws IOException on I/O error
     */
    public long sizeOfMetadata() throws IOException {
        if (!Files.exists(metadataIndex)) {
            return 0;
        }
        return Files.size(metadataIndex);
    }

    /**
     * @return size of all proof/java/key files in the cache
     * @throws IOException on I/O error
     */
    public long sizeOfCacheFiles() throws IOException {
        if (!Files.exists(cacheIndex)) {
            return 0;
        }
        // simple: sum the size of all files in ~/.key/cachedProofs
        try (var entries = Files.list(cacheIndex)) {
            var filesToSum = entries.filter(x -> !Files.isDirectory(x)).toList();
            long total = 0;
            for (var file : filesToSum) {
                total += Files.size(file);
            }
            return total;
        }
    }

    /**
     * Get the size of the proof that is referenced in the cached proof branch.
     *
     * @param cachedProofBranch some cached proof branch
     * @return size of proof + size of referenced files
     * @throws IOException on I/O error
     */
    public long sizeOfCachedProof(CachedProofBranch cachedProofBranch) throws IOException {
        // size is determined by proof file size + referenced file size
        long sum = 0;
        sum += Files.size(cachedProofBranch.proofFile);
        for (var referencedFile : cachedProofBranch.getReferencedFiles()) {
            sum += Files.size(referencedFile.file());
        }
        return sum;
    }
}
