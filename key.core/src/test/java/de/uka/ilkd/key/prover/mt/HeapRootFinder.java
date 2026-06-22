/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.lang.management.ManagementFactory;
import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;

/**
 * In-process, MAT-free "path to GC roots" finder. Seeds a breadth-first search from the static
 * fields of every loaded class (discovered via the {@code gcClassHistogram} diagnostic command) and
 * walks the object graph by reflection until it reaches a given target object, then prints the
 * shortest static-rooted reference chain. Used by {@link MtRetentionProbe} to name the exact static
 * field/cache pinning a disposed {@code Proof}.
 *
 * <p>
 * The target is held only in a stack local of the caller, never in a static or in any field
 * reachable
 * from a static, so the only chain this search can find is the genuine leak path.
 */
final class HeapRootFinder {

    private HeapRootFinder() {}

    /** edge to the object that referenced this one, plus a human label for the edge. */
    private record Edge(Object parent, String label) {
    }

    static void reportPath(Object target) {
        System.out.println("[root] searching for static path to " + brief(target));
        IdentityHashMap<Object, Edge> parent = new IdentityHashMap<>();
        ArrayDeque<Object> queue = new ArrayDeque<>();

        // ---- seed from static fields of every loaded class ----
        int seeded = 0;
        for (String cn : loadedClassNames()) {
            Class<?> c;
            try {
                c = Class.forName(cn, false, HeapRootFinder.class.getClassLoader());
            } catch (Throwable t) {
                continue;
            }
            for (Field f : declaredFieldsSafe(c)) {
                if (!Modifier.isStatic(f.getModifiers()) || f.getType().isPrimitive()) {
                    continue;
                }
                Object v = readStatic(f);
                if (v == null) {
                    continue;
                }
                if (parent.containsKey(v)) {
                    continue;
                }
                parent.put(v, new Edge(null, c.getName() + "." + f.getName()));
                if (v == target) {
                    printChain(parent, target);
                    return;
                }
                queue.add(v);
                seeded++;
            }
        }
        System.out.println("[root] seeded " + seeded + " static roots");

        // ---- seed from live threads and their thread-locals ----
        int threadSeeds = 0;
        for (Thread t : Thread.getAllStackTraces().keySet()) {
            for (Object v : threadRoots(t)) {
                if (v == null || parent.containsKey(v)) {
                    continue;
                }
                parent.put(v, new Edge(null, "Thread[" + t.getName() + "] threadLocal/field"));
                if (v == target) {
                    printChain(parent, target);
                    return;
                }
                queue.add(v);
                threadSeeds++;
            }
        }
        System.out.println(
            "[root] seeded " + threadSeeds + " thread roots; walking graph...");

        // ---- BFS over the object graph ----
        long visited = 0;
        while (!queue.isEmpty()) {
            Object cur = queue.poll();
            visited++;
            for (Edge e : children(cur)) {
                Object child = e.parent(); // here Edge.parent holds the child value
                if (child == null || parent.containsKey(child)) {
                    continue;
                }
                parent.put(child, new Edge(cur, e.label()));
                if (child == target) {
                    System.out.println("[root] found after visiting " + visited + " objects");
                    printChain(parent, target);
                    return;
                }
                if (traversable(child)) {
                    queue.add(child);
                }
            }
        }
        System.out.println("[root] NO static path found after visiting " + visited
            + " objects (target is not statically reachable, or is held by a thread/JNI root)");
    }

    /** Returns the outgoing references of {@code o} as (child, label) pairs (reusing Edge). */
    private static List<Edge> children(Object o) {
        List<Edge> out = new ArrayList<>();
        Class<?> c = o.getClass();
        if (c.isArray()) {
            if (!c.getComponentType().isPrimitive()) {
                int n = Array.getLength(o);
                for (int i = 0; i < n; i++) {
                    Object v = Array.get(o, i);
                    if (v != null) {
                        out.add(new Edge(v, "[" + i + "]"));
                    }
                }
            }
            return out;
        }
        boolean isRef = o instanceof java.lang.ref.Reference;
        for (Class<?> k = c; k != null && k != Object.class; k = k.getSuperclass()) {
            for (Field f : declaredFieldsSafe(k)) {
                if (Modifier.isStatic(f.getModifiers()) || f.getType().isPrimitive()) {
                    continue;
                }
                // Exclude weak/soft/phantom edges: only report a strong retention path.
                if (isRef && f.getName().equals("referent")) {
                    continue;
                }
                Object v = readInstance(f, o);
                if (v != null) {
                    out.add(new Edge(v, "." + f.getName()));
                }
            }
        }
        return out;
    }

    /** Skip walking through huge value-type fan-outs that can't be a short root path. */
    private static boolean traversable(Object o) {
        return !(o instanceof String) && !(o instanceof Number) && !(o instanceof Boolean)
                && !(o instanceof Character) && !(o instanceof Class);
    }

    private static void printChain(IdentityHashMap<Object, Edge> parent, Object target) {
        ArrayList<String> chain = new ArrayList<>();
        Object node = target;
        Edge e = parent.get(node);
        chain.add(brief(node));
        while (e != null && e.parent() != null) {
            chain.add(e.label() + "  ->  " + brief(e.parent()));
            node = e.parent();
            e = parent.get(node);
        }
        if (e != null) {
            chain.add("[static root] " + e.label());
        }
        System.out.println("[root] ===== PATH TO GC ROOT (root first) =====");
        for (int i = chain.size() - 1; i >= 0; i--) {
            System.out.println("[root]   " + chain.get(i));
        }
    }

    private static String brief(Object o) {
        if (o == null) {
            return "null";
        }
        String cn = o.getClass().getName();
        String extra = "";
        try {
            if (o.getClass().isArray()) {
                extra = "[len=" + Array.getLength(o) + "]";
            }
        } catch (Throwable ignore) {
            // ignore
        }
        return cn + "@" + Integer.toHexString(System.identityHashCode(o)) + extra;
    }

    private static Field[] declaredFieldsSafe(Class<?> c) {
        try {
            return c.getDeclaredFields();
        } catch (Throwable t) {
            return new Field[0];
        }
    }

    private static Object readStatic(Field f) {
        try {
            f.setAccessible(true);
            return f.get(null);
        } catch (Throwable t) {
            return null;
        }
    }

    private static Object readInstance(Field f, Object o) {
        try {
            f.setAccessible(true);
            return f.get(o);
        } catch (Throwable t) {
            return null;
        }
    }

    /** ThreadLocal values + non-primitive instance fields of a thread (its target, locals map). */
    private static List<Object> threadRoots(Thread t) {
        List<Object> out = new ArrayList<>();
        // instance fields of the Thread object itself (e.g. the Runnable target)
        for (Field f : declaredFieldsSafe(Thread.class)) {
            if (Modifier.isStatic(f.getModifiers()) || f.getType().isPrimitive()) {
                continue;
            }
            Object v = readInstance(f, t);
            if (v != null) {
                out.add(v);
            }
        }
        // ThreadLocalMap entries (both thread-local and inheritable)
        for (String mapField : new String[] { "threadLocals", "inheritableThreadLocals" }) {
            try {
                Field f = Thread.class.getDeclaredField(mapField);
                f.setAccessible(true);
                Object map = f.get(t);
                if (map == null) {
                    continue;
                }
                Field tableF = map.getClass().getDeclaredField("table");
                tableF.setAccessible(true);
                Object table = tableF.get(map);
                if (table == null) {
                    continue;
                }
                int n = Array.getLength(table);
                Field valF = null;
                for (int i = 0; i < n; i++) {
                    Object entry = Array.get(table, i);
                    if (entry == null) {
                        continue;
                    }
                    if (valF == null) {
                        valF = entry.getClass().getDeclaredField("value");
                        valF.setAccessible(true);
                    }
                    Object val = valF.get(entry);
                    if (val != null) {
                        out.add(val);
                    }
                }
            } catch (Throwable ignore) {
                // field layout differs or inaccessible
            }
        }
        return out;
    }

    private static List<String> loadedClassNames() {
        List<String> names = new ArrayList<>();
        try {
            String out = (String) ManagementFactory.getPlatformMBeanServer().invoke(
                new javax.management.ObjectName("com.sun.management:type=DiagnosticCommand"),
                "gcClassHistogram", new Object[] { new String[0] },
                new String[] { String[].class.getName() });
            for (String line : out.split("\n")) {
                String[] p = line.trim().split("\\s+");
                if (p.length >= 4 && p[0].endsWith(":")) {
                    String name = p[3];
                    if (name.startsWith("[") || name.contains("/")) {
                        continue; // arrays, lambdas/hidden classes
                    }
                    names.add(name);
                }
            }
        } catch (Exception e) {
            System.out.println("[root] class enumeration failed: " + e);
        }
        return names;
    }
}
