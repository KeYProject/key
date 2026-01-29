package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.logic.JTerm;
import org.jspecify.annotations.Nullable;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.logic.origin.OriginRefType;
import org.key_project.util.collection.ImmutableList;

import java.util.Collection;
import java.util.Optional;

/**
 * This class represents a single reference to a heap
 * Such a reference is build from a list of heap-update terms
 */
public class HeapReference {
    public enum HeapUpdateType {
        INITIAL("INIT"),
        STORE("STORE"),
        ANON("ANON"),
        HEAP("HEAP"),
        INDIRECT("FWD");

        public final String key;

        HeapUpdateType(String k) {
            key= k;
        }

        @Override
        public String toString() {
            return key;
        }
    }

    public static class HeapUpdate {
        public final HeapUpdateType type;
        public final JTerm term1;
        public final JTerm term2;
        public final JTerm term3;
        public final @Nullable OriginRef Origin;

        public HeapUpdate(HeapUpdateType type, JTerm term1, JTerm term2, JTerm term3, @Nullable OriginRef origin) {
            this.type = type;
            this.term1 = term1;
            this.term2 = term2;
            this.term3 = term3;
            Origin = origin;
        }
    }

    public final ImmutableList<HeapUpdate> updates;

    public HeapReference(ImmutableList<HeapUpdate> updates) {
        this.updates = updates;
    }

    public HeapReference(Collection<HeapUpdate> updates) {
        this.updates = ImmutableList.fromList(updates);
    }

    public Optional<Integer> getLineNumber(PositionInfo methodPosition) {

        int methodStart = 1;
        if (methodPosition != null) {
            methodStart = methodPosition.getStartPosition().line();
        }

        int ln = -1;
        for (var p : this.updates) {
            switch (p.type) {
                case INITIAL:
                    if (p.Origin != null && p.Origin.hasFile()) {
                        ln = Math.max(ln, p.Origin.LineEnd);
                    } else {
                        ln = Math.max(ln, methodStart);
                    }

                    break;
                case STORE:
                case ANON:
                case HEAP:
                case INDIRECT:
                    if (p.Origin != null && p.Origin.hasFile()) {
                        ln = Math.max(ln, p.Origin.LineEnd);
                    }
                    break;
            }
        }
        if (ln < 0) return Optional.empty();
        return Optional.of(ln);
    }

    public static HeapReference.HeapUpdate newStoreUpdate(JTerm t) {
        var origin = t.getOriginRef().
            stream().
            filter(p -> p.Type == OriginRefType.JAVA_STMT || p.Type == OriginRefType.LOOP_ANONUPDATE || p.Type == OriginRefType.OPERATION_ANONUPDATE).
            findFirst().
            orElse(null);
        return new HeapUpdate(HeapUpdateType.STORE, t.sub(1), t.sub(2), t.sub(3), origin);
    }

    public static HeapReference.HeapUpdate newAnonUpdate(JTerm t) {
        var origin = t.getOriginRef().
                stream().
                filter(p -> p.Type == OriginRefType.JAVA_STMT || p.Type == OriginRefType.LOOP_ANONUPDATE || p.Type == OriginRefType.OPERATION_ANONUPDATE).
                filter(p -> p.hasFile()).
                findFirst().
                orElse(null);
        return new HeapUpdate(HeapUpdateType.ANON, t.sub(1), t.sub(2), null, origin);
    }

    public static HeapUpdate newIndirect(JTerm t) {
        return new HeapUpdate(HeapUpdateType.INDIRECT, t, null, null, null);
    }

    public static HeapUpdate newHeap(JTerm t) {
        var origin = t.getOriginRef().
                stream().
                filter(p -> p.Type == OriginRefType.JAVA_STMT || p.Type == OriginRefType.LOOP_ANONUPDATE || p.Type == OriginRefType.OPERATION_ANONUPDATE).
                findFirst().
                orElse(null);

        if (origin == null && t.op().name().toString().equalsIgnoreCase("heap")) {
            return new HeapUpdate(HeapUpdateType.INITIAL, t, null, null, null);
        }

        return new HeapUpdate(HeapUpdateType.HEAP, t, null, null, origin);
    }

    public boolean heapEquals(HeapReference other) {
        var ln1 = this.getLineNumber(null);
        var ln2 = other.getLineNumber(null);

        if (ln1.isPresent() && ln2.isPresent()) {
            return ln1.get().equals(ln2.get());
        }

        if (ln1.isEmpty() && ln2.isEmpty()) {
            return true;
        }

        return false;
    }
}
