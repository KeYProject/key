/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.fail;

/**
 * Guards the strategy's cost machinery against remembering state between calls.
 * <p>
 * A strategy, and therefore the whole tree of {@code Feature}s it evaluates, is built once per
 * proof and shared by every goal. Under the multi-core prover several worker threads evaluate that
 * feature tree at the same time, so a {@code Feature} (or a term generator / projection / choice
 * point it uses) must be <em>stateless</em>: any mutable instance field on it is shared mutable
 * state that two workers race. Per-evaluation state belongs in the per-call {@code MutableState}
 * (as {@code ForEachCP} keeps its current term) or in local variables, never in a field of the
 * shared feature. This is exactly the mistake that {@code OneOfCP.theChosenOne} was: an instance
 * field holding the chosen branch on a shared feature, which two workers overwrote for each other.
 * <p>
 * This test scans the compiled classes of the proving-path packages, keeps those that implement one
 * of the shared cost-machinery interfaces, and fails when it finds
 * <ul>
 * <li>a non-{@code final} instance field, or</li>
 * <li>a {@code final} instance field holding a plain mutable collection.</li>
 * </ul>
 * Fields that are safe by design (immutable content built once in the constructor, per-call helper
 * objects, ...) are listed in {@code shared-feature-state-allowlist.txt} with a one-line
 * justification. The static-field companion is {@code SharedStateLintTest}; this one covers the
 * instance fields on the shared strategy machinery, which the static scan cannot see.
 */
public final class FeatureStatelessnessLintTest {

    /** Packages that hold the strategy cost machinery. */
    private static final String[] SCANNED_PACKAGES = {
        "de.uka.ilkd.key.strategy",
        "org.key_project.prover.strategy",
    };

    /**
     * The interfaces whose implementors are built once into the shared feature tree and evaluated
     * concurrently. An implementor of any of these must carry no mutable instance state.
     */
    private static final String[] SHARED_MACHINERY_INTERFACES = {
        "org.key_project.prover.strategy.costbased.feature.Feature",
        "org.key_project.prover.strategy.costbased.termfeature.TermFeature",
        "org.key_project.prover.strategy.costbased.termgenerator.TermGenerator",
        "org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm",
        "org.key_project.prover.strategy.costbased.feature.instantiator.ChoicePoint",
    };

    /** Mutable collection types that are unsafe to share as the value of a final field. */
    private static final Class<?>[] MUTABLE_VALUE_TYPES = {
        java.util.HashMap.class, java.util.HashSet.class, java.util.ArrayList.class,
        java.util.LinkedList.class, java.util.LinkedHashMap.class, java.util.LinkedHashSet.class,
        java.util.WeakHashMap.class, java.util.IdentityHashMap.class, java.util.TreeMap.class,
        java.util.TreeSet.class, java.util.ArrayDeque.class, java.util.EnumMap.class,
        java.util.PriorityQueue.class,
    };

    @Test
    public void sharedCostMachineryCarriesNoMutableInstanceState() throws Exception {
        final List<Class<?>> machinery = new ArrayList<>();
        for (String iface : SHARED_MACHINERY_INTERFACES) {
            try {
                machinery.add(Class.forName(iface, false, getClass().getClassLoader()));
            } catch (Throwable t) {
                // an interface module not on the classpath here is simply not scanned
            }
        }

        final Set<String> allowlist = readAllowlist();
        final Set<String> staleAllowlist = new TreeSet<>(allowlist);
        final List<String> violations = new ArrayList<>();
        final List<String> unreadable = new ArrayList<>();

        for (String className : scannedClassNames()) {
            final Class<?> clazz;
            try {
                clazz = Class.forName(className, false, getClass().getClassLoader());
            } catch (Throwable t) {
                unreadable.add(className + " (" + t + ")");
                continue;
            }
            if (clazz.isInterface() || !implementsAny(clazz, machinery)) {
                continue;
            }
            for (Field field : declaredFieldsOf(clazz, unreadable)) {
                if (Modifier.isStatic(field.getModifiers()) || field.isSynthetic()) {
                    continue;
                }
                final String problem = judge(field);
                if (problem == null) {
                    continue;
                }
                final String id = clazz.getName() + "#" + field.getName();
                if (allowlist.contains(id)) {
                    staleAllowlist.remove(id);
                    continue;
                }
                violations.add(id + "\n      " + problem);
            }
        }

        staleAllowlist.removeIf(e -> unreadable.stream().anyMatch(u -> u.startsWith(className(e))));
        if (!staleAllowlist.isEmpty()) {
            violations.add("stale allowlist entries (field gone or no longer a finding): "
                + staleAllowlist);
        }
        if (!violations.isEmpty()) {
            fail(adviceMessage(violations));
        }
    }

    /** @return a description of the problem, or {@code null} if the field is fine */
    private static String judge(Field field) {
        if (!Modifier.isFinal(field.getModifiers())) {
            return "non-final instance field on a shared cost-machinery object: two worker threads "
                + "evaluating this feature write it at the same time. Move per-evaluation state "
                + "into the MutableState (see ForEachCP), or make the field final and immutable.";
        }
        // Instance fields have no instance to read here, so we can only judge the DECLARED type.
        // Flag a field only when its declared type is itself a concrete mutable collection
        // (private final HashMap ...); a field declared as an interface (Map/List/Set) might hold a
        // thread-safe value, so it is left to review / the static lint rather than flagged here.
        final Class<?> declared = field.getType();
        for (Class<?> mutable : MUTABLE_VALUE_TYPES) {
            if (mutable.isAssignableFrom(declared)) {
                return "final instance field whose declared type is a plain mutable "
                    + declared.getSimpleName() + ": if it is written during evaluation, workers "
                    + "race it. Use a concurrent/immutable collection, or allowlist it if it is "
                    + "built once in the constructor and only read afterwards.";
            }
        }
        return null;
    }

    private static boolean implementsAny(Class<?> clazz, List<Class<?>> interfaces) {
        for (Class<?> iface : interfaces) {
            if (iface.isAssignableFrom(clazz)) {
                return true;
            }
        }
        return false;
    }

    private static Field[] declaredFieldsOf(Class<?> clazz, List<String> unreadable) {
        try {
            return clazz.getDeclaredFields();
        } catch (Throwable t) {
            unreadable.add(clazz.getName() + " (" + t + ")");
            return new Field[0];
        }
    }

    private static Set<String> scannedClassNames() throws Exception {
        final URL codeSource =
            de.uka.ilkd.key.proof.Goal.class.getProtectionDomain().getCodeSource().getLocation();
        final Path classesRoot = Path.of(codeSource.toURI());
        if (!Files.isDirectory(classesRoot)) {
            throw new IllegalStateException("expected a classes directory, got: " + classesRoot);
        }
        // the strategy machinery lives in key.core and in key.ncore.calculus; scan both class roots
        final List<Path> roots = new ArrayList<>();
        roots.add(classesRoot);
        final Path ncoreCalculus = classesRoot.getParent().getParent().getParent().getParent()
                .getParent().resolve("key.ncore.calculus/build/classes/java/main");
        if (Files.isDirectory(ncoreCalculus)) {
            roots.add(ncoreCalculus);
        }
        final Set<String> result = new TreeSet<>();
        for (Path root : roots) {
            for (String pkg : SCANNED_PACKAGES) {
                final Path pkgDir = root.resolve(pkg.replace('.', '/'));
                if (!Files.isDirectory(pkgDir)) {
                    continue;
                }
                try (Stream<Path> files = Files.walk(pkgDir)) {
                    files.filter(p -> p.toString().endsWith(".class"))
                            .map(p -> root.relativize(p).toString()
                                    .replace(java.io.File.separatorChar, '.')
                                    .replaceAll("\\.class$", ""))
                            .forEach(result::add);
                }
            }
        }
        return result;
    }

    private static Set<String> readAllowlist() throws IOException {
        final Set<String> allowlist = new HashSet<>();
        final InputStream in = FeatureStatelessnessLintTest.class
                .getResourceAsStream("shared-feature-state-allowlist.txt");
        if (in == null) {
            return allowlist;
        }
        try (BufferedReader reader =
            new BufferedReader(new InputStreamReader(in, StandardCharsets.UTF_8))) {
            String line;
            while ((line = reader.readLine()) != null) {
                final String trimmed = line.trim();
                if (trimmed.isEmpty() || trimmed.startsWith("#")) {
                    continue;
                }
                allowlist.add(trimmed.split("\\s+")[0]);
            }
        }
        return allowlist;
    }

    private static String className(String id) {
        final int hash = id.indexOf('#');
        return hash < 0 ? id : id.substring(0, hash);
    }

    private static String adviceMessage(List<String> violations) {
        final StringBuilder sb = new StringBuilder(1500);
        sb.append("Mutable state on shared strategy cost machinery (").append(violations.size())
                .append(" finding(s)).\n\n")
                .append(
                    "A strategy's feature tree is built once per proof and evaluated by several\n")
                .append(
                    "worker threads at once under the multi-core prover. A Feature (or its term\n")
                .append("generator / projection / choice point) must therefore keep NO mutable\n")
                .append("instance state -- two workers would race it (this is what OneOfCP's\n")
                .append("theChosenOne field was).\n\nFindings:\n");
        for (String v : violations) {
            sb.append("  - ").append(v).append('\n');
        }
        sb.append("\nHow to fix:\n")
                .append("  * per-evaluation state  -> the per-call MutableState (see ForEachCP)\n")
                .append("  * a fill-once lookup     -> final field + immutable content\n")
                .append(
                    "  * genuinely safe field   -> add it to shared-feature-state-allowlist.txt\n")
                .append(
                    "                              (same package as this test) with a reason.\n")
                .append("See key.core/src/main/java/de/uka/ilkd/key/prover/README.md, rule 2.");
        return sb.toString();
    }
}
