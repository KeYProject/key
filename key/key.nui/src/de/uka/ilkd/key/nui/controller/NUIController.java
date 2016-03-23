package de.uka.ilkd.key.nui.controller;

import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.DataModel;
import de.uka.ilkd.key.nui.NUI;

/**
 * Abstract common base class for all controllers.
 * 
 * @author Florian Breitfelder
 *
 */
@SuppressWarnings("PMD.AtLeastOneConstructor")
public abstract class NUIController {

    /**
     * The bundle used for internationalization of text strings.
     */
    protected ResourceBundle bundle;
    /**
     * The fx:id of the controller.
     */
    protected String componentName;

    /**
     * The data model linked to application.
     */
    protected DataModel dataModel;

    /**
     * The filename of the associated FXML file.
     */
    protected String filename;

    /**
     * A reference to the {@link NUI} which manages the main application.
     */
    protected NUI nui;

    /**
     * Replaces the usual java constructor, because JavaFX does not allow to use
     * user-defined constructors.
     * 
     * @param nuiRef
     *            A reference to the {@link NUI} which manages the main
     *            application.
     * @param dataModel
     *            The data model linked to application.
     * @param bundle
     *            The bundle used for internationalization of text strings.
     * @param componentName
     *            The fx:id of the controller.
     * @param filename
     *            The filename of the associated FXML file.
     */
    public void constructor(final NUI nuiRef, final DataModel dataModel,
            final ResourceBundle bundle, final String componentName, final String filename) {
        this.nui = nuiRef;
        this.dataModel = dataModel;
        this.bundle = bundle;
        this.componentName = componentName;
        this.filename = filename;

        init();
    }

    /**
     * Getter.
     * @return the {@link ResourceBundle}.
     */
    public ResourceBundle getBundle() {
        return bundle;
    }

    /**
     * Getter.
     * @return the componentName as {@link String}.
     */
    public String getComponentName() {
        return componentName;
    }

    /**
     * Getter.
     * @return the {@link DataModel}.
     */
    public DataModel getDataModel() {
        return dataModel;
    }

    /**
     * Getter.
     * @return the filename as {@link String}.
     */
    public String getFilename() {
        return filename;
    }

    /**
     * Getter.
     * @return the {@link NUI}.
     */
    public NUI getNui() {
        return nui;
    }

    /**
     * Getter.
     * @param bundle the {@link ResourceBundle} to set.
     */
    public void setBundle(final ResourceBundle bundle) {
        this.bundle = bundle;
    }

    /**
     * Setter.
     * @param componentName the {@link String} to set.
     */
    public void setComponentName(final String componentName) {
        this.componentName = componentName;
    }

    /**
     * Setter.
     * @param dataModel the {@link DataModel} to set.
     */
    public void setDataModel(final DataModel dataModel) {
        this.dataModel = dataModel;
    }

    /**
     * Setter.
     * @param filename the {@link String} to set.
     */
    public void setFilename(final String filename) {
        this.filename = filename;
    }

    /**
     * Setter.
     * @param nui the {@link NUI} to set.
     */
    public void setNui(final NUI nui) {
        this.nui = nui;
    }

    /**
     * This method initializes the controller and can be used to perform actions
     * right after creating the controller.
     */
    protected abstract void init();

}
