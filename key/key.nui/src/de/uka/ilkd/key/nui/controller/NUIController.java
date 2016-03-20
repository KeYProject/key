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
     * TODO
     * @return
     */
    public ResourceBundle getBundle() {
        return bundle;
    }
    /**
     * TODO
     * @return
     */
    public String getComponentName() {
        return componentName;
    }
    /**
     * TODO
     * @return
     */
    public DataModel getDataModel() {
        return dataModel;
    }
    /**
     * TODO
     * @return
     */
    public String getFilename() {
        return filename;
    }
    /**
     * TODO
     * @return
     */
    public NUI getNui() {
        return nui;
    }
    /**
     * TODO
     * @param bundle
     */
    public void setBundle(final ResourceBundle bundle) {
        this.bundle = bundle;
    }
    /**
     * TODO
     * @param componentName
     */
    public void setComponentName(final String componentName) {
        this.componentName = componentName;
    }
    /**
     * TODO
     * @param dataModel
     */
    public void setDataModel(final DataModel dataModel) {
        this.dataModel = dataModel;
    }
    /**
     * TODO
     * @param filename
     */
    public void setFilename(final String filename) {
        this.filename = filename;
    }
    /**
     * TODO
     * @param nui
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
