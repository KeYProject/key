/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.label;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Iterator;
import java.util.Set;
import java.util.TreeSet;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofSettings;

import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableArray;

import org.junit.jupiter.api.Test;

/**
 * Regression harness for the term-label reworking (equality flip + LabeledTermImpl/TermImpl
 * merge). It replays a curated set of console-style KeY proofs and writes, for every proof node,
 * a canonical serialization of the sequent <em>including all term labels at every subterm</em>.
 *
 * <p>
 * The dump is written to the directory given by the {@code labeldump.dir} system property (default
 * a temp dir). Running this test on two revisions and diffing the two output directories proves
 * that the change did not alter any sequent or any term label anywhere in these proofs. The test
 * also records which term labels were actually observed ({@code _labels_seen.txt}) so label
 * coverage is established from real data rather than assumed.
 * </p>
 *
 * <p>
 * This is intentionally driven by an explicit, hand-written term serializer rather than
 * {@link Object#toString()} so that label capture does not depend on any pretty-printer.
 * </p>
 */
public class TermLabelEquivalenceDumpTest {

    /**
     * Proof files relative to the repository root. Chosen to be replayable headlessly and to
     * collectively exercise the term labels registered by the plain {@code JavaProfile} (origin,
     * anonHeap, selectSK, ...). Labels used only by the symbolic_execution / proof_references
     * modules are deliberately out of scope.
     */
    private static final String[] PROOFS = {
        // heap / JML operation & dependency contracts (anonHeap, selectSK, impl, origin, ...)
        "key.ui/examples/heap/observer/ExampleObserver_ExampleObserver.key.proof",
        "key.ui/examples/heap/observer/ExampleSubject_ExampleSubject.key.proof",
        "key.ui/examples/heap/observer/ExampleSubject_notifyObservers.key.proof",
        "key.ui/examples/heap/observer/ExampleSubject_inv.key.proof",
        "key.ui/examples/heap/observer/ExampleSubject_change.key.proof",
        "key.ui/examples/heap/observer/ExampleObserver_value.key.proof",
        "key.ui/examples/heap/observer/ExampleSubject_addObserver.key.proof",
        "key.ui/examples/heap/observer/ExampleSubject_value_dep.key.proof",
        "key.ui/examples/heap/observer/ExampleObserver_update.key.proof",
        "key.ui/examples/heap/verifyThis11_1_Maximum/project.key.proof",
        "key.ui/examples/heap/coincidence_count/project.key.proof",
        "key.ui/examples/heap/fm12_01_LRS/lcp.key.proof",
        "key.ui/examples/heap/permutedSum/perm.proof",
        "key.ui/examples/heap/BoyerMoore/BM(BM__monoLemma((I,int,int)).JML normal_behavior operation contract.0.proof",
        // java_dl / arithmetic / bit operations (loopScopeIndex, SC, ...)
        "key.ui/examples/standard_key/java_dl/recursion/triangular.proof",
        "key.ui/examples/standard_key/arith/jdivevenodd.key.proof",
        "key.ui/examples/standard_key/bitoperations/exBitwiseOr1.key.proof",
    };

    /**
     * Term labels that are actually attached during standard (console) proof search and therefore
     * must be observed while replaying {@link #PROOFS}. Note: {@code postCondition}, {@code undef}
     * and {@code selfComposedExecution} are attached only by the information-flow module
     * (key.core.infflow) and {@code Trigger} only by the SMT translation, so none of them is
     * reachable by replaying standard Java profile proofs; the infflow labels are covered by the
     * separate testRunAllInfProofs regression instead.
     */
    private static final Set<String> EXPECTED_LABELS = Set.of(
        "origin", "anonHeapFunction", "selectSK", "impl", "SC", "loopScopeIndex");

    @Test
    public void dumpAllProofSequents() throws Exception {
        final Path dumpDir = Paths.get(System.getProperty("key.labeldump.dir",
            System.getProperty("java.io.tmpdir") + "/labeldump"));
        Files.createDirectories(dumpDir);
        final Path root = repoRoot();

        // origin labels are user-facing and only attached when this setting is on
        ProofSettings.DEFAULT_SETTINGS.getTermLabelSettings().setUseOriginLabels(true);

        final Set<String> labelsSeen = new TreeSet<>();
        final StringBuilder index = new StringBuilder();
        int loaded = 0;
        for (String rel : PROOFS) {
            final Path pf = root.resolve(rel);
            if (!Files.exists(pf)) {
                index.append("MISSING ").append(rel).append('\n');
                continue;
            }
            KeYEnvironment<?> env = null;
            try {
                env = KeYEnvironment.load(pf);
                final Proof proof = env.getLoadedProof();
                final StringBuilder sb = new StringBuilder();
                int nodes = 0;
                final Iterator<Node> it = proof.root().subtreeIterator();
                while (it.hasNext()) {
                    final Node n = it.next();
                    sb.append("=== node ").append(n.serialNr()).append(" ===\n");
                    dumpSequent(n.sequent(), sb, labelsSeen);
                    nodes++;
                }
                Files.writeString(dumpDir.resolve(dumpName(rel)), sb.toString());
                index.append("OK ").append(nodes).append(" nodes  ").append(rel).append('\n');
                loaded++;
            } catch (Exception e) {
                index.append("FAILED ").append(rel).append("  : ").append(e).append('\n');
            } finally {
                if (env != null) {
                    env.dispose();
                }
            }
        }
        Files.writeString(dumpDir.resolve("_index.txt"), index.toString());
        Files.writeString(dumpDir.resolve("_labels_seen.txt"), String.join("\n", labelsSeen));
        System.out.println("[labeldump] wrote " + loaded + "/" + PROOFS.length
            + " proof dumps to " + dumpDir);
        System.out.println("[labeldump] labels observed: " + labelsSeen);

        org.junit.jupiter.api.Assertions.assertTrue(loaded >= 15,
            "expected at least 15 of the curated proofs to replay, got " + loaded);
        org.junit.jupiter.api.Assertions.assertTrue(labelsSeen.containsAll(EXPECTED_LABELS),
            "term-label coverage regressed; expected " + EXPECTED_LABELS + " but saw "
                + labelsSeen);
    }

    private static void dumpSequent(Sequent seq, StringBuilder sb, Set<String> labelsSeen) {
        for (SequentFormula sf : seq.antecedent()) {
            dumpTerm((JTerm) sf.formula(), sb, labelsSeen);
            sb.append('\n');
        }
        sb.append("==>\n");
        for (SequentFormula sf : seq.succedent()) {
            dumpTerm((JTerm) sf.formula(), sb, labelsSeen);
            sb.append('\n');
        }
    }

    /** Recursively serialize a term, emitting the (sorted) label set at every node. */
    private static void dumpTerm(JTerm t, StringBuilder sb, Set<String> labelsSeen) {
        sb.append(t.op().name());
        if (t.hasLabels()) {
            final ImmutableArray<TermLabel> labels = t.getLabels();
            final TreeSet<String> here = new TreeSet<>();
            for (int i = 0, sz = labels.size(); i < sz; i++) {
                final String s = labels.get(i).toString();
                here.add(s);
                labelsSeen.add(labels.get(i).name().toString());
            }
            sb.append("<<").append(String.join(",", here)).append(">>");
        }
        if (!t.boundVars().isEmpty()) {
            sb.append('{').append(t.boundVars()).append('}');
        }
        if (t.arity() > 0) {
            sb.append('(');
            for (int i = 0; i < t.arity(); i++) {
                if (i > 0) {
                    sb.append(',');
                }
                dumpTerm(t.sub(i), sb, labelsSeen);
            }
            sb.append(')');
        }
    }

    private static String dumpName(String rel) {
        return rel.replaceAll("[^A-Za-z0-9._-]", "_") + ".dump";
    }

    /** Walk up from the working directory until the KeY example tree is found. */
    private static Path repoRoot() {
        Path p = Paths.get("").toAbsolutePath();
        while (p != null) {
            if (Files.exists(p.resolve("key.ui/examples/heap"))) {
                return p;
            }
            p = p.getParent();
        }
        throw new IllegalStateException("could not locate repository root from "
            + Paths.get("").toAbsolutePath());
    }
}
