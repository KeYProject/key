package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.logic.ITermLabel;

/**
 * A positionedString with labels, which can then be passed over to the translated term.
 * For the moment, this is used to distinguish implicit specifications from explicit ones
 * and '&' from '&&' (logical and shortcut 'and') as well as '|' from '||' (logical and
 * shortcut 'or').
 * Cf. {@link de.uka.ilkd.key.logic.TermImpl} and {@link de.uka.ilkd.key.logic.LabeledTermImpl}.
 *
 * @author Michael Kirsten
 */
public class PositionedLabeledString extends PositionedString {

    public final ImmutableArray<ITermLabel> labels;

    public PositionedLabeledString(String text, String fileName, Position pos,
                                   ImmutableArray<ITermLabel> labels) {
        super(text, fileName, pos);        
        assert labels != null : "Term labels must not be null";
        assert !labels.isEmpty() : "There must be at least one term label";
        this.labels = labels;
        
    }

    public PositionedLabeledString(String text, String fileName, Position pos, ITermLabel label) {
        this(text, fileName, pos, new ImmutableArray<ITermLabel>(label));
    }

    public PositionedLabeledString(String text, String fileName, ImmutableArray<ITermLabel> labels) {
        this(text, fileName, null, labels);
    }

    public PositionedLabeledString(String text, String fileName, ITermLabel label) {
        this(text, fileName, new ImmutableArray<ITermLabel>(label));
    }

    public PositionedLabeledString(String text, ImmutableArray<ITermLabel> labels) {
        this(text, (String)null, labels);
    }

    public PositionedLabeledString(String text, ITermLabel label) {
        this(text, new ImmutableArray<ITermLabel>(label));
    }

    /**
     * {@inheritDoc}
     */
    public boolean hasLabels() {
            return true;
    }

    /**
     * returns the labels attached to this positioned string
     */
    @Override
    public ImmutableArray<ITermLabel> getLabels() {
            return labels;
    }

    /**
     * returns true if the given label is attached
     * @param label the ITermLabel for which to look (must not be null)
     * @return true iff. the label is attached to this positioned string
     */
    @Override
    public boolean containsLabel(ITermLabel label) {
            assert label != null : "Label must not be null";
            for (ITermLabel l : labels) {
                    if (label.equals(l)) {
                            return true;
                    }
            }
            return false;
    }

    /**
     * {@inheritDoc}
     */
    public boolean equals(Object o) {
            if (!(o instanceof PositionedLabeledString)) {
                    return false;
            }
            final PositionedLabeledString cmp = (PositionedLabeledString) o;
            if (labels.size() == cmp.labels.size()) {
                    if (!super.equals(o)) {
                            return false;
                    }
                    for (ITermLabel l : labels) { // this is not optimal, but as long as number of labels limited ok
                            if (!cmp.labels.contains(l)) {
                                    return false;
                            }
                    }
                    return true;
            }
            return false;
    }

    /**
     * {@inheritDoc}
     */
    public int hashCode() {
            return super.hashCode() * 17 + labels.hashCode();
    }

    /**
     * {@inheritDoc}
     */
    public String toString() {
            StringBuilder result = new StringBuilder(super.toString());
            result.append("<<");
            // as labels must not be empty at least one element exists
            result.append(labels.get(0).toString()); 
            for (int i = 1; i<labels.size();i++) {
                    result.append(", \"");
                    result.append(labels.get(i).toString());                        
     result.append("\"");
            }               
            result.append(">>");
            return result.toString();
    }
}