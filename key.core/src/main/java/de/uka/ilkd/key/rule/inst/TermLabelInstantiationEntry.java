package de.uka.ilkd.key.rule.inst;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.label.TermLabel;

/**
 *
 *
 */
public class TermLabelInstantiationEntry extends InstantiationEntry<ImmutableArray<TermLabel>> {

    TermLabelInstantiationEntry(ImmutableArray<TermLabel> labels) {
        super(labels);
    }

    /**
     * {@inheritDoc}
     */
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(getInstantiation());
        sb.append('\n');
        return sb.toString();
    }

}
