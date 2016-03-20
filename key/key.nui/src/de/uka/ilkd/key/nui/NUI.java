package de.uka.ilkd.key.nui;

import java.io.File;
import java.io.IOException;
import java.lang.annotation.Annotation;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Map;
import java.util.PropertyResourceBundle;
import java.util.ResourceBundle;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

import de.uka.ilkd.key.nui.controller.ControllerAnnotation;
import de.uka.ilkd.key.nui.controller.MainViewController;
import de.uka.ilkd.key.nui.controller.MainViewController.Place;
import de.uka.ilkd.key.nui.controller.NUIController;
import de.uka.ilkd.key.nui.controller.TreeViewController;
import de.uka.ilkd.key.nui.exceptions.ComponentNotFoundException;
import de.uka.ilkd.key.nui.exceptions.ControllerNotFoundException;
import de.uka.ilkd.key.nui.exceptions.ToggleGroupNotFoundException;
import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.scene.Scene;
import javafx.scene.control.Menu;
import javafx.scene.control.RadioMenuItem;
import javafx.scene.control.ToggleGroup;
import javafx.scene.image.Image;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.Pane;
import javafx.stage.Stage;

/**
 * Main Class for initializing the GUI.
 * 
 * @author Florian Breitfelder
 * @author Patrick Jattke
 *
 */
public class NUI extends Application {

    /**
     * The proof file initially (at program startup) loaded.
     */
    private static File initialProofFile;

    /**
     * Contains references to all loaded controllers, where <br \>
     * <ul>
     * <li>String is the fx:id of the loaded controller.
     * <li>NUIController is the reference to the loaded controller.
     * </ul>
     */
    private final Map<String, NUIController> controllers = new HashMap<>();

    /**
     * Contains the loaded components, where
     * <ul>
     * <li>String represents the fx:id of the loaded component.
     * <li>Pane is the reference to the loaded component.
     * </ul>
     */
    private final Map<String, Pane> components = new HashMap<>();

    /**
     * Contains the loaded toggle groups, where
     * <ul>
     * <li>String represents the fx:id of the loaded toggle group.
     * <li>ToggleGroup is the reference to the loaded toggle group.
     * </ul>
     */
    private final Map<String, ToggleGroup> toggleGroups = new HashMap<>();

    /**
     * The currently loaded resource bundle (language file).
     */
    private ResourceBundle bundle;

    /**
     * The root border pane where all others components get loaded in.
     */
    private BorderPane root;

    /**
     * A reference to the {@link MainViewController}.
     */
    private MainViewController mainViewCont;

    /**
     * The menu "View" of the menu bar.
     */
    private Menu viewPositionMenu;

    /**
     * The filename of the mainView, without extension (.fxml).
     */
    private static final String MAINVIEW_FILENAME = "MainView";

    /**
     * Directory containing the component files (.fxml).
     */
    private static final String COMPONENTS_DIR = "components";

    /**
     * The data model used to store the loaded proof as a {@link TreeViewState}.
     */
    private DataModel dataModel;

    /**
     * The main method.
     * 
     * @param args
     *            The arguments passed to the program. Can take the path to a
     *            proof file as argument, which is loaded right after program
     *            startup.
     */
    public static void main(final String... args) {
        if (args.length != 0) {
            initialProofFile = new File(System.getProperty("user.dir") + args[0]);
        }
        launch(args);
    }

    /**
     * When program is starting method "start" is called. Loads the stage and
     * scene.
     */
    @Override
    public final void start(final Stage stage) {
        try {
            initializeNUI();
        }
        catch (IOException | ComponentNotFoundException | ControllerNotFoundException e2) {
            e2.printStackTrace();
        }

        // Load scene and set preferences
        final Scene scene = new Scene(root, 1024, 768);
        stage.setTitle("KeY");
        stage.getIcons().add(new Image(getClass().getResourceAsStream("images/KeY-Mono.png")));
        stage.setScene(scene);
        stage.show();

        // Assign event when stage closing event is elevated
        stage.setOnCloseRequest((windowEvent) -> {
            try {
                ((MainViewController) getController(MAINVIEW_FILENAME))
                        .handleCloseWindow(windowEvent);
            }
            catch (ControllerNotFoundException e1) {
                e1.showMessage();
            }
        });
    }

    /**
     * Initializes the application, such as all components, all controllers and
     * views.
     *
     * @throws IOException
     * @throws ComponentNotFoundException
     * @throws ControllerNotFoundException
     */
    public void initializeNUI()
            throws IOException, ComponentNotFoundException, ControllerNotFoundException {
        // Load Main View
        final String filename = MAINVIEW_FILENAME + ".fxml";

        bundle = new PropertyResourceBundle(
                getClass().getResourceAsStream("bundle_en_EN.properties"));
        dataModel = new DataModel(this, bundle);
        final FXMLLoader fxmlLoader = new FXMLLoader(getClass().getResource(filename), bundle);
        System.out.println("start launched successfully.");
        root = fxmlLoader.load();
        components.put(MAINVIEW_FILENAME, root);

        mainViewCont = fxmlLoader.getController();
        mainViewCont.constructor(this, dataModel, bundle, MAINVIEW_FILENAME, filename);
        controllers.put(MAINVIEW_FILENAME, mainViewCont);

        // initialize viewPositionMenu
        viewPositionMenu = new Menu(bundle.getString("configViews"));
        viewPositionMenu.setId("configViews");

        // Load all components
        loadComponents();

        ((TreeViewController) getController("treeViewPane"))
                .addSearchView(getComponent("searchViewPane"), getController("searchViewPane"));
        // create file menu for MainView
        mainViewCont.getViewMenu().getItems().add(viewPositionMenu);

        // place component on MainView
        mainViewCont.addComponent(getComponent("treeViewPane"), Place.LEFT);
        mainViewCont.addComponent(getComponent("proofViewPane"), Place.MIDDLE);
        mainViewCont.addComponent(getComponent("strategyViewPane"), Place.RIGHT);
        mainViewCont.addComponent(getComponent("openProofsViewPane"), Place.BOTTOM);
    }

    /**
     * Loads the FXML components and stores the references to
     * <ul>
     * <li>the controllers in {@link #controllers}
     * <li>the components in {@link #components}
     * <li>the toggle groups in {@link #toggleGroups}.
     * </ul>
     * 
     * @exception IOException
     */
    private void loadComponents() throws IOException {
        final File jarFile = new File(
                getClass().getProtectionDomain().getCodeSource().getLocation().getPath());
        if (jarFile.isFile()) { // Run with JAR file
            final JarFile jar = new JarFile(jarFile);
            final Enumeration<JarEntry> entries = jar.entries();
            while (entries.hasMoreElements()) {
                final String fileName = entries.nextElement().getName();
                if (fileName.matches("(de/uka/ilkd/key/nui/" + COMPONENTS_DIR + "/).*(.fxml)")) {
                    loadComponent(
                            fileName.substring(fileName.lastIndexOf('/') + 1, fileName.length()));
                }
            }
            jar.close();
        }

        else {// Run with IDE
            final File[] files = new File(getClass().getResource(COMPONENTS_DIR).getPath())
                    .listFiles();

            for (final File file : files) {
                if (file.isFile() && file.getName().matches(".*[.fxml]")) {
                    loadComponent(file.getName());
                }
            }
        }
    }

    /**
     * Loads the component with the given filename.
     * 
     * @param fileName
     *            The filename of the component to load.
     * @throws IOException
     */
    private void loadComponent(final String fileName) throws IOException {
        final FXMLLoader fxmlLoader = new FXMLLoader(
                getClass().getResource(COMPONENTS_DIR + File.separator + fileName), bundle);

        // String componentName = cutFileExtension(file.getName());
        final Pane component = fxmlLoader.load();
        components.put(component.getId(), component);
        // before you can get the controller
        // you have to call fxmlLoader.load()
        final NUIController nuiController = fxmlLoader.getController();
        if (nuiController != null) {
            nuiController.constructor(this, dataModel, bundle, component.getId(), fileName);

            controllers.put(component.getId(), nuiController);

            final Annotation[] annotations = nuiController.getClass().getAnnotations();

            // create a view position menu for every component
            if (annotations != null) {
                for (final Annotation annotation : annotations) {
                    if (annotation instanceof ControllerAnnotation) {
                        final ControllerAnnotation ctrlAnnotation = (ControllerAnnotation) annotation;
                        if (ctrlAnnotation.createMenu()) {
                            final ToggleGroup toggleGroup = new ToggleGroup();
                            toggleGroups.put(component.getId(), toggleGroup);
                            viewPositionMenu.getItems()
                                    .add(createSubMenu(component.getId(), toggleGroup));
                            break;
                        }
                    }
                }
            }
        } else {
            throw new RuntimeException();
        }
    }

    /**
     * Creates sub menu entries for the "View" menu.
     * 
     * @param menuName
     *            The name of the menu where sub menu should be added to.
     * @param toggleGroup
     *            The toggle group containing the sub menu entries.
     * @return The constructed Menu.
     */
    private Menu createSubMenu(final String menuName, final ToggleGroup toggleGroup) {
        final Menu menu = new Menu(bundle.getString(menuName));
        final String hideText = bundle.getString("hide");
        final String leftText = bundle.getString("left");
        final String rightText = bundle.getString("right");
        final String bottomText = bundle.getString("bottom");
        final String middleText = bundle.getString("middle");

        addRadioMenuItem(hideText, menuName, toggleGroup, true, Place.HIDDEN, menu);

        addRadioMenuItem(leftText, menuName, toggleGroup, false, Place.LEFT, menu);

        addRadioMenuItem(rightText, menuName, toggleGroup, false, Place.RIGHT, menu);

        addRadioMenuItem(bottomText, menuName, toggleGroup, false, Place.BOTTOM, menu);

        addRadioMenuItem(middleText, menuName, toggleGroup, false, Place.MIDDLE, menu);

        return menu;
    }

    /**
     * Creates a radio menu item entry and adds it to the given Menu
     * <code>destinationMenu</code>.
     * 
     * @param menuItemName
     *            The fx:id and shown name of the menu entry.
     * @param componentName
     *            The component name associated with.
     * @param tGroup
     *            The toggle group where the item belongs to.
     * @param isSelected
     *            Specifies whether the item is selected by default or not.
     * @param position
     *            The position of the view associated with the menu item entry.
     * @param destinationMenu
     *            The destination menu where the menu item should be added to.
     */
    private void addRadioMenuItem(final String menuItemName, final String componentName,
            final ToggleGroup tGroup, final Boolean isSelected, final Place position,
            final Menu destinationMenu) {
        final RadioMenuItem menuItem = new RadioMenuItem(menuItemName);
        menuItem.setOnAction(mainViewCont.getNewHandleLoadComponent());
        menuItem.setId(menuItemName);
        menuItem.getProperties().put("componentName", componentName);
        menuItem.setToggleGroup(tGroup);
        menuItem.setSelected(isSelected);
        menuItem.setUserData(position);
        destinationMenu.getItems().add(menuItem);
    }

    /**
     * Returns the component with the specified fx:id of the list of loaded
     * components {@link #components}.
     * 
     * @param name
     *            The fx:id of the component.
     * @return A reference to a pane corresponding to the given fx:id.
     * @throws ComponentNotFoundException
     *             If no component with the given fx:id was found.
     */
    public Pane getComponent(final String name) throws ComponentNotFoundException {
        if (!components.containsKey(name)) {
            throw new ComponentNotFoundException(name);
        }
        return components.get(name);
    }

    /**
     * Returns the controller with the specified fx:id of the list of loaded
     * controller {@link #controllers}.
     * 
     * @param name
     *            The fx:id of the controller.
     * @return A subclass of NUIController, which is a reference to the
     *         controller.
     * @throws ControllerNotFoundException
     *             Iff there was no controller with the given fx:id loaded.
     */
    public NUIController getController(final String name) throws ControllerNotFoundException {
        if (!controllers.containsKey(name)) {
            throw new ControllerNotFoundException(name);
        }
        return controllers.get(name);
    }

    /**
     * Returns the toggle group with the given fx:id.
     * 
     * @param name
     *            The fx:id of the toggle group.
     * @return The toggle group with the given fx:id.
     * @throws ToggleGroupNotFoundException
     *             Iff there was no toggle group with the given fx:id loaded.
     */
    public ToggleGroup getToggleGroup(final String name) throws ToggleGroupNotFoundException {
        if (!toggleGroups.containsKey(name)) {
            throw new ToggleGroupNotFoundException(name);
        }
        return toggleGroups.get(name);
    }

    /**
     * Returns the main border pane containing all other components.
     * 
     * @return BorderPane where all other components are in.
     */
    public BorderPane getRoot() {
        return root;
    }

    /**
     * Returns the proof file initially loaded.
     * 
     * @return initialProofFile the proof file initially loaded
     */
    public static File getInitialProofFile() {
        return initialProofFile;
    }

    /**
     * Updates the status bar on the mainView by the given text. Keeps the text
     * on the status bar till the next update is performed.
     * 
     * @param text
     *            String to be set to the status bar.
     */
    public void updateStatusbar(final String text) {
        try {
            ((MainViewController) getController(MAINVIEW_FILENAME)).updateStatusbar(text);
        }
        catch (ControllerNotFoundException e) {
            e.showMessage();
        }
    }

    /**
     * Returns a reference to the DataModel.
     * 
     * @return dataModel
     */
    public DataModel getDataModel() {
        return dataModel;
    }

    /**
     * Returns the text from the language file which corresponds to the textId.
     * 
     * @param textId
     *            The key associated with the text to be searched for.
     * @return The text string associated with the key.
     */
    public String getText(final String textId) {
        return bundle.getString(textId);
    }
}
