package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.op.SchemaVariable;

/**
 * 
 * 
 */
public class TermLabelInstantiationEntry extends InstantiationEntry {

    private final ImmutableArray<ITermLabel> labels;

    TermLabelInstantiationEntry(SchemaVariable sv, ImmutableArray<ITermLabel> labels) {
        super(sv);
        this.labels = labels;
    }

    /**
     * {@inheritDoc}
     */
    @Override   
    public Object getInstantiation() {
        return labels;
    }
    
    /**
     * {@inheritDoc}
     */
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(getSchemaVariable());
        sb.append(": ");
        sb.append(getInstantiation());
        sb.append('\n');
        return sb.toString();
    }

}
