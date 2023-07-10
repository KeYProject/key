package de.uka.ilkd.key.gui.plugins.caching;

/**
 * Interface to receive callbacks from the {@link ReferenceSearchDialog}.
 *
 * @author Arne Keller
 */
public interface ReferenceSearchDialogListener {
    /**
     * Button to close the dialog has been activated.
     */
    void closeButtonClicked(ReferenceSearchDialog dialog);

    /**
     * Button to copy proof steps has been activated.
     */
    void copyButtonClicked(ReferenceSearchDialog dialog);
}
