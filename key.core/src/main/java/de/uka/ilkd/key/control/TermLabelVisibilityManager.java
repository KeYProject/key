package de.uka.ilkd.key.control;

import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.control.event.TermLabelVisibilityManagerEvent;
import de.uka.ilkd.key.control.event.TermLabelVisibilityManagerListener;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;

public class TermLabelVisibilityManager implements VisibleTermLabels {

    /**
     * The names of all term labels that should not be printed by default.
     */
    private static final Name[] HIDDEN_BY_DEFAULT = {};

    /**
     * The names of all term labels that should never be printed.
     */
    private static final Name[] ALWAYS_HIDDEN = { OriginTermLabel.NAME };

    /**
     * A switch to choose whether labels are to be shown or not.
     */
    private boolean showLabels = true;

    /**
     * The names of all term labels that should not be printed, this contains also the labels in
     * {@link TermLabelVisibilityManager#HIDDEN_BY_DEFAULT}.
     */
    private final Set<Name> hiddenLabels = new HashSet<Name>();

    /**
     * All available {@link TermLabelVisibilityManagerListener}s.
     */
    private final List<TermLabelVisibilityManagerListener> listeners =
        new LinkedList<TermLabelVisibilityManagerListener>();

    /**
     * Constructs a new TermLabelVisibilityManager.
     */
    public TermLabelVisibilityManager() {
        for (Name name : HIDDEN_BY_DEFAULT) {
            hiddenLabels.add(name);
        }


        for (Name name : ALWAYS_HIDDEN) {
            hiddenLabels.add(name);
        }
    }

    /**
     * Gives the information whether currently term labels should be shown or not.
     *
     * @return A boolean value whether currently term labels should be shown.
     */
    public boolean isShowLabels() {
        return showLabels;
    }

    /**
     * Set the switch whether term labels should be shown to passed value.
     *
     * @param showLabels A boolean value whether term labels should be shown
     */
    public void setShowLabels(boolean showLabels) {
        if (this.showLabels != showLabels) {
            this.showLabels = showLabels;
            fireVisibleLabelsChanged(new TermLabelVisibilityManagerEvent(this));
        }
    }

    /**
     * Gives the information whether the term label with the passed name is currently hidden.
     *
     * @param labelName The name of a term label
     * @return A boolean value whether the investigated term label is hidden.
     */
    public boolean isHidden(Name labelName) {
        return hiddenLabels.contains(labelName);
    }

    /**
     * Sets the state of the term label with the passed name to hidden or not.
     *
     * @param labelName The name of a term label
     * @param hidden The boolean value whether the term label should be hidden or not
     */
    public void setHidden(Name labelName, boolean hidden) {
        if (hidden) {
            if (hiddenLabels.add(labelName)) {
                fireVisibleLabelsChanged(new TermLabelVisibilityManagerEvent(this));
            }
        } else {
            if (hiddenLabels.remove(labelName)) {
                fireVisibleLabelsChanged(new TermLabelVisibilityManagerEvent(this));
            }
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean contains(TermLabel label) {
        return label != null && contains(label.name());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean contains(Name labelName) {
        if (showLabels) {
            return !hiddenLabels.contains(labelName);
        } else {
            return false;
        }
    }

    /**
     * Registers the given {@link TermLabelVisibilityManagerListener}.
     *
     * @param l The {@link TermLabelVisibilityManagerListener} to add.
     */
    public void addTermLabelVisibilityManagerListener(TermLabelVisibilityManagerListener l) {
        if (l != null) {
            listeners.add(l);
        }
    }

    /**
     * Unregisters the given {@link TermLabelVisibilityManagerListener}.
     *
     * @param l The {@link TermLabelVisibilityManagerListener} to remove.
     */
    public void removeTermLabelVisibilityManagerListener(TermLabelVisibilityManagerListener l) {
        if (l != null) {
            listeners.remove(l);
        }
    }

    /**
     * Returns all available {@link TermLabelVisibilityManagerListener}.
     *
     * @return all available {@link TermLabelVisibilityManagerListener}.
     */
    public TermLabelVisibilityManagerListener[] getTermLabelVisibilityManagerListeners() {
        return listeners.toArray(new TermLabelVisibilityManagerListener[listeners.size()]);
    }

    /**
     * Fires the event
     * {@link TermLabelVisibilityManagerListener#visibleLabelsChanged( TermLabelVisibilityManagerEvent)}
     * to all listeners.
     *
     * @param e The event object.
     */
    protected void fireVisibleLabelsChanged(TermLabelVisibilityManagerEvent e) {
        TermLabelVisibilityManagerListener[] listener = getTermLabelVisibilityManagerListeners();
        for (TermLabelVisibilityManagerListener l : listener) {
            l.visibleLabelsChanged(e);
        }
    }

    /**
     * Returns a sorted list of all term label names supported by the given {@link Proof}.
     *
     * @param proof The given {@link Proof}.
     * @return The sorted list of supported term label names.
     */
    public static List<Name> getSortedTermLabelNames(Proof proof) {
        return getSortedTermLabelNames(proof.getServices().getProfile());
    }

    /**
     * Returns a sorted list of all term label names supported by the given {@link Profile}.
     *
     * @param profile The given {@link Profile}.
     * @return The sorted list of supported term label names.
     */
    public static List<Name> getSortedTermLabelNames(Profile profile) {
        return getSortedTermLabelNames(profile.getTermLabelManager());
    }

    /**
     * Returns a sorted list of all term TermLabelManager names supported by the given
     * {@link TermLabelManager}.
     *
     * @param manager The given {@link Profile}.
     * @return The sorted list of supported term label names.
     */
    public static List<Name> getSortedTermLabelNames(TermLabelManager manager) {
        List<Name> labelNames = manager.getSupportedTermLabelNames().toList();

        Collections.sort(labelNames, new Comparator<Name>() {
            @Override
            public int compare(Name t, Name t1) {
                return String.CASE_INSENSITIVE_ORDER.compare(t.toString(), t1.toString());
            }
        });

        return labelNames;
    }
}
