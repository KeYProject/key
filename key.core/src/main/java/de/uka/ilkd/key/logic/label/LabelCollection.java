package de.uka.ilkd.key.logic.label;

import org.key_project.util.collection.ImmutableArray;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.function.Predicate;

public class LabelCollection {

    private final LinkedHashSet<TermLabel> labels = new LinkedHashSet<>();
    private boolean changed;

    public LabelCollection(ImmutableArray<TermLabel> p_labels) {
        for (int i = 0, sz = p_labels.size(); i < sz; i++) {
            labels.add(p_labels.get(i));
        }
        changed = false;
    }

    public void add(TermLabel label) {
        changed |= labels.add(label);
    }

    public void remove(TermLabel label) {
        changed |= labels.remove(label);
    }

    public boolean hasChanged() {
        return changed;
    }

    public boolean contains(TermLabel label) {
        return labels.contains(label);
    }

    public Collection<TermLabel> getLabels() {
        return labels;
    }

    public void removeIf(Predicate<TermLabel> p) {
        changed |= labels.removeIf(p);
    }

    public <S> S getFirst(Class<S> termLabelClass) {
        for (var label : labels) {
            if (termLabelClass.isInstance(label)) {
                return (S) label;
            }
        }
        return null;
    }

    // only for tests
    public void replaceWith(Collection<TermLabel> newLabels, boolean p_changed) {
        labels.clear();
        labels.addAll(newLabels);
        changed = p_changed;
    }
}
