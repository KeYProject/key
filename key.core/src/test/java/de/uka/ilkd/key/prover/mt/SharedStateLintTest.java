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
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.fail;

/**
 * Guards the proving path against shared mutable static state.
 * <p>
 * The multi-core prover runs proof search on several worker threads. A {@code static} field
 * exists once for the whole program, so every worker reads and writes the same object. A plain
 * {@code HashMap}, {@code ArrayList} or a non-{@code final} static field in rule, strategy or
 * proof code is therefore a data race waiting to happen: two workers writing at the same moment
 * can lose entries, compute wrong costs, or crash.
 * <p>
 * This test scans the compiled classes of the proving-path packages, in {@code key.core} and in
 * the {@code key.ncore.matcher} match framework alike, and fails when it finds
 * <ul>
 * <li>a non-{@code final} static field, or</li>
 * <li>a {@code final} static field whose value is a plain mutable collection
 * ({@code HashMap}, {@code HashSet}, {@code ArrayList}, ...).</li>
 * </ul>
 * Fields that are safe by design (settings written only before proving starts, collections
 * guarded by an external lock, ...) are listed in {@code shared-state-allowlist.txt} next to this
 * test, each with a one-line justification. How to fix a genuine finding is described in
 * {@code key.core/src/main/java/de/uka/ilkd/key/prover/README.md} (in one line: cache whose value
 * depends only on the key &rarr; {@code StripedLruCache}; cache whose value depends on when it was
 * stored &rarr; {@code ConcurrentLruCache}; per-thread scratch memory &rarr; {@code ThreadLocal};
 * fill-once lookup table &rarr; {@code final} + immutable content).
 */
public final class SharedStateLintTest {

    /** Packages of {@code key.core} that run during proof search (the "proving path"). */
    private static final String[] SCANNED_CORE_PACKAGES = {
        "de.uka.ilkd.key.rule",
        "de.uka.ilkd.key.strategy",
        "de.uka.ilkd.key.proof",
        "de.uka.ilkd.key.logic",
        "de.uka.ilkd.key.prover",
    };

    /**
     * Packages of {@code key.ncore.matcher} that run during proof search: every taclet match goes
     * through the match framework, so it is as much on the proving path as the {@code key.core}
     * packages above. It lives in its own module, hence its own classes directory to walk.
     */
    private static final String[] SCANNED_MATCHER_PACKAGES = {
        "org.key_project.prover.rules.matcher",
    };

    /**
     * Runtime classes that are safe to share between threads. A field whose value is an instance
     * of one of these (or lives in one of these packages) passes the lint.
     */
    private static final String[] SANCTIONED_VALUE_CLASSES = {
        "java.util.concurrent.", // ConcurrentHashMap, CopyOnWriteArrayList, atomics, ...
        "java.util.Collections$Synchronized",
        "java.util.Collections$Unmodifiable",
        "java.util.Collections$Empty",
        "java.util.Collections$Singleton",
        "java.util.ImmutableCollections", // List.of(...), Map.of(...), Map.copyOf(...)
        "org.key_project.util.ConcurrentLruCache",
        "org.key_project.util.StripedLruCache",
    };

    /** Value classes that are mutable and not safe to share without extra protection. */
    private static final Class<?>[] MUTABLE_VALUE_TYPES = {
        java.util.HashMap.class, java.util.HashSet.class, java.util.ArrayList.class,
        java.util.LinkedList.class, java.util.LinkedHashMap.class, java.util.LinkedHashSet.class,
        java.util.WeakHashMap.class, java.util.IdentityHashMap.class, java.util.TreeMap.class,
        java.util.TreeSet.class, java.util.ArrayDeque.class, java.util.EnumMap.class,
        java.util.PriorityQueue.class, java.util.Stack.class, java.util.BitSet.class,
        StringBuilder.class,
    };

    @Test
    public void provingPathHasNoUnprotectedSharedStaticState() throws Exception {
        final Set<String> allowlist = readAllowlist();
        final List<String> violations = new ArrayList<>();
        final List<String> unreadable = new ArrayList<>();
        final Set<String> staleAllowlistEntries = new TreeSet<>(allowlist);

        for (String className : scannedClassNames()) {
            final Class<?> clazz;
            try {
                // without initialization first: looking at field declarations does not need
                // static initializers to run
                clazz = Class.forName(className, false, getClass().getClassLoader());
            } catch (Throwable t) {
                unreadable.add(className + " (" + t + ")");
                continue;
            }
            for (Field field : declaredFieldsOf(clazz, unreadable)) {
                if (!Modifier.isStatic(field.getModifiers()) || field.isSynthetic()) {
                    continue;
                }
                final String id = clazz.getName() + "#" + field.getName();
                final String problem = judge(field, unreadable);
                if (problem == null) {
                    continue;
                }
                if (allowlist.contains(id)) {
                    staleAllowlistEntries.remove(id);
                    continue;
                }
                violations.add(id + "\n      " + problem);
            }
        }
        // an allowlist entry that no longer matches a finding is stale and must be removed,
        // otherwise the list silently rots
        staleAllowlistEntries.removeIf(e -> violationsMissingBecauseUnreadable(e, unreadable));
        if (!staleAllowlistEntries.isEmpty()) {
            violations.add("stale allowlist entries (field gone or no longer a finding): "
                + staleAllowlistEntries);
        }

        if (!violations.isEmpty()) {
            fail(adviceMessage(violations, unreadable));
        }
    }

    /**
     * Decides whether the field is a lint finding.
     *
     * @return a human-readable problem description, or {@code null} if the field is fine
     */
    private static String judge(Field field, List<String> unreadable) {
        if (!Modifier.isFinal(field.getModifiers())) {
            return "non-final static field: every worker thread sees and may write this one "
                + "field. Make it final (and its content immutable), or use one of the patterns "
                + "from the table in prover/README.md.";
        }
        // final field: the reference cannot change, but the object it points to may still be
        // mutable. Only container-like declared types need a value inspection.
        final Class<?> declared = field.getType();
        if (!Collection.class.isAssignableFrom(declared) && !Map.class.isAssignableFrom(declared)
                && declared != Object.class && !isMutableValueType(declared)) {
            return null;
        }
        final Object value;
        try {
            field.setAccessible(true);
            value = field.get(null); // triggers the static initializer if not yet run
        } catch (Throwable t) {
            unreadable.add(field.getDeclaringClass().getName() + "#" + field.getName()
                + " (" + t + ")");
            return null;
        }
        if (value == null || isSanctioned(value.getClass())) {
            return null;
        }
        if (isMutableValueType(value.getClass())) {
            return "final static field holding a plain mutable " + value.getClass().getSimpleName()
                + ": the reference is fixed but several worker threads still write the same "
                + "object. Use the table in prover/README.md to pick a thread-safe replacement.";
        }
        return null;
    }

    private static boolean isMutableValueType(Class<?> c) {
        for (Class<?> mutable : MUTABLE_VALUE_TYPES) {
            if (mutable.isAssignableFrom(c)) {
                return true;
            }
        }
        return false;
    }

    private static boolean isSanctioned(Class<?> c) {
        if (ThreadLocal.class.isAssignableFrom(c)) {
            return true;
        }
        final String name = c.getName();
        for (String sanctioned : SANCTIONED_VALUE_CLASSES) {
            if (name.startsWith(sanctioned)) {
                return true;
            }
        }
        return false;
    }

    private static Field[] declaredFieldsOf(Class<?> clazz, List<String> unreadable) {
        try {
            return clazz.getDeclaredFields();
        } catch (Throwable t) { // e.g. NoClassDefFoundError for optional dependencies
            unreadable.add(clazz.getName() + " (" + t + ")");
            return new Field[0];
        }
    }

    /** Enumerates the class names of the scanned packages, per module. */
    private static Set<String> scannedClassNames() throws Exception {
        final Set<String> result = new TreeSet<>();
        // each module contributes its own classes directory; an anchor class locates it
        collectClassNames(de.uka.ilkd.key.proof.Goal.class, SCANNED_CORE_PACKAGES, result);
        collectClassNames(org.key_project.prover.rules.matcher.vm.VMProgramInterpreter.class,
            SCANNED_MATCHER_PACKAGES, result);
        return result;
    }

    /**
     * Adds the class names of {@code packages} to {@code out}, read from the classes directory of
     * the module that {@code moduleAnchor} belongs to.
     *
     * @param moduleAnchor any class of the module to scan
     * @param packages the packages to walk, as declared above
     * @param out collects the fully qualified class names
     */
    private static void collectClassNames(Class<?> moduleAnchor, String[] packages,
            Set<String> out) throws Exception {
        // a module is on the test classpath either as its classes directory (the module the test
        // itself lives in) or as its jar (a module dependency)
        final URL codeSource = moduleAnchor.getProtectionDomain().getCodeSource().getLocation();
        final Path root = Path.of(codeSource.toURI());
        for (String pkg : packages) {
            final Set<String> found = Files.isDirectory(root) ? classNamesFromDirectory(root, pkg)
                    : classNamesFromJar(root, pkg);
            // a scanned package without classes means the code moved and this guard silently
            // stopped covering it -- the same rot the stale-allowlist check above prevents
            if (found.isEmpty()) {
                throw new IllegalStateException("scanned package " + pkg + " has no classes in "
                    + root + ": update the scanned packages of this test to follow the code");
            }
            out.addAll(found);
        }
    }

    private static Set<String> classNamesFromDirectory(Path classesRoot, String pkg)
            throws IOException {
        final Path pkgDir = classesRoot.resolve(pkg.replace('.', '/'));
        if (!Files.isDirectory(pkgDir)) {
            return Set.of();
        }
        try (Stream<Path> files = Files.walk(pkgDir)) {
            return files.filter(p -> p.toString().endsWith(".class"))
                    .map(p -> classesRoot.relativize(p).toString()
                            .replace(java.io.File.separatorChar, '.')
                            .replaceAll("\\.class$", ""))
                    .collect(Collectors.toCollection(TreeSet::new));
        }
    }

    private static Set<String> classNamesFromJar(Path jarPath, String pkg) throws IOException {
        final String prefix = pkg.replace('.', '/') + "/";
        try (JarFile jar = new JarFile(jarPath.toFile())) {
            return jar.stream().map(JarEntry::getName)
                    .filter(n -> n.startsWith(prefix) && n.endsWith(".class"))
                    .map(n -> n.replace('/', '.').replaceAll("\\.class$", ""))
                    .collect(Collectors.toCollection(TreeSet::new));
        }
    }

    private static Set<String> readAllowlist() throws IOException {
        final Set<String> allowlist = new HashSet<>();
        final InputStream in =
            SharedStateLintTest.class.getResourceAsStream("shared-state-allowlist.txt");
        if (in == null) {
            return allowlist;
        }
        try (BufferedReader reader =
            new BufferedReader(new InputStreamReader(in, StandardCharsets.UTF_8))) {
            String line;
            while ((line = reader.readLine()) != null) {
                final String trimmed = line.trim();
                // '#' also separates class from field inside an entry, so comments are
                // whole-line only ('#' first) and a justification is everything after the
                // first whitespace
                if (trimmed.isEmpty() || trimmed.startsWith("#")) {
                    continue;
                }
                allowlist.add(trimmed.split("\\s+")[0]);
            }
        }
        return allowlist;
    }

    private static boolean violationsMissingBecauseUnreadable(String entry,
            List<String> unreadable) {
        final String className = entry.substring(0, Math.max(entry.indexOf('#'), 0));
        return unreadable.stream().anyMatch(u -> u.startsWith(className));
    }

    private static String adviceMessage(List<String> violations, List<String> unreadable) {
        final StringBuilder sb = new StringBuilder(2048);
        sb.append("Shared mutable static state on the proving path (")
                .append(violations.size()).append(" finding(s)).\n\n")
                .append("The multi-core prover runs proof search on several worker threads at\n")
                .append("once. A static field exists once for the whole program, so every worker\n")
                .append("reads and writes the same object -- for a plain mutable field that is a\n")
                .append("data race: entries get lost, costs come out wrong, proofs fail\n")
                .append("nondeterministically.\n\nFindings:\n");
        for (String v : violations) {
            sb.append("  - ").append(v).append('\n');
        }
        sb.append("\nHow to fix (details and a decision table in\n")
                .append("key.core/src/main/java/de/uka/ilkd/key/prover/README.md):\n")
                .append("  * value depends only on the key            -> StripedLruCache\n")
                .append("  * value depends on when it was stored      -> ConcurrentLruCache\n")
                .append("  * per-thread scratch / last-call memo      -> ThreadLocal\n")
                .append(
                    "  * filled once, then only read              -> final + immutable content\n")
                .append("\nIf the field is safe by design (e.g. a setting written only before\n")
                .append("proving starts), add a line to shared-state-allowlist.txt (same package\n")
                .append("as SharedStateLintTest, test resources) with a short justification.\n");
        if (!unreadable.isEmpty()) {
            sb.append("\nNote: ").append(unreadable.size())
                    .append(" class(es)/field(s) could not be inspected (first three): ")
                    .append(unreadable.subList(0, Math.min(3, unreadable.size())));
        }
        return sb.toString();
    }
}
