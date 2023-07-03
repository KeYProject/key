package de.uka.ilkd.key.gui.plugins.caching;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
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
public class CachingDatabase {

    private static final Logger LOGGER = LoggerFactory.getLogger(CachingDatabase.class);
    private static final Random RAND = new Random();

    private static boolean initDone = false;
    private static boolean dirty = false;
    private static List<CachedProofBranch> cache;

    private CachingDatabase() {

    }

    public static void init() {
        if (initDone) {
            return;
        }
        initDone = true;
        cache = new ArrayList<>();

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
     *
     * @param proof the proof to store
     */
    public static void addProof(Proof proof) throws IOException {
        init();
        dirty = true;

        // save to file in ~/.key/cachedProofs/
        PathConfig.getCacheDirectory().mkdirs();
        File file;
        do {
            var filename = "proof" + (RAND.nextInt(1000000)) + ".proof";
            file = new File(PathConfig.getCacheDirectory(), filename);
        } while (file.exists());
        proof.saveToFile(file);

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
}
