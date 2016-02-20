package de.uka.ilkd.key.nui;

import java.io.File;
import java.util.HashMap;
import java.util.PropertyResourceBundle;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.controller.MainViewController;
import de.uka.ilkd.key.nui.controller.MainViewController.Place;
import de.uka.ilkd.key.nui.controller.NUIController;
import de.uka.ilkd.key.nui.exceptions.ComponentNotFoundException;
import de.uka.ilkd.key.nui.exceptions.ControllerNotFoundException;
import de.uka.ilkd.key.nui.exceptions.ToggleGroupNotFoundException;
import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.scene.Scene;
import javafx.scene.control.Menu;
import javafx.scene.control.RadioMenuItem;
import javafx.scene.control.ToggleGroup;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.Pane;
import javafx.stage.Stage;

/**
 * Main Class for initializing the GUI.
 * 
 * @author Florian Breitfelder
 *
 */
public class NUI extends Application {

    /**
     * The proof file initially (at program startup) loaded.
     */
    private static File initialProofFile;

    /**
     * The main method.
     * 
     * @param args
     *            The arguments passed to the program.
     */
    public static void main(final String... args) {
        if (args.length != 0) {
            initialProofFile = new File(
                    System.getProperty("user.dir") + args[0]);
        }
        launch(args);
    }

    private HashMap<String, NUIController> controllers = new HashMap<String, NUIController>();
    private HashMap<String, Pane> components = new HashMap<String, Pane>();
    private HashMap<String, ToggleGroup> toggleGroups = new HashMap<String, ToggleGroup>();

    private ResourceBundle bundle = null;
    private BorderPane root = null;
    private FXMLLoader fxmlLoader = null;
    private MainViewController mainViewController = null;

    private Menu viewPositionMenu = null;
    private DataModel dataModel = new DataModel();

    /**
     * When program is starting method "start" is called.
     */
    @Override
    public final void start(final Stage stage) throws Exception {
        // Load Main View
        String filename = "MainView.fxml";
        String name = cutFileExtension(filename);

        bundle = new PropertyResourceBundle(
                getClass().getResourceAsStream("bundle_en_EN.properties"));
        fxmlLoader = new FXMLLoader(getClass().getResource(filename), bundle);
        System.out.println("start launched successfully.");
        root = fxmlLoader.load();
        components.put("MainView", root);

        mainViewController = fxmlLoader.getController();
        mainViewController.constructor(this, name, filename);
        controllers.put("MainView", mainViewController);

        // initialize viewPositionMenu
        viewPositionMenu = new Menu(bundle.getString("configViews"));

        // Load all components
        loadComponents();

        // create file menu for MainView
        mainViewController.getViewMenu().getItems().add(viewPositionMenu);

        // place component on MainView
        mainViewController.placeComponent("treeView", Place.LEFT);
        mainViewController.placeComponent("proofView", Place.RIGHT);
        mainViewController.placeComponent("openProofsView", Place.MIDDLE);

        // Load scene and set preferences
        final Scene scene = new Scene(root);
        stage.setTitle("KeY");
        stage.setScene(scene);
        stage.show();
    }

    private void loadComponents() throws Exception {
        File[] files = new File(getClass().getResource("components").getPath())
                .listFiles();
        FXMLLoader fxmlLoader = null;
        for (File file : files) {
            if (file.isFile() && file.getName().matches(".*[.fxml]")) {
                fxmlLoader = new FXMLLoader(
                        getClass().getResource("components/" + file.getName()));

                String componentName = cutFileExtension(file.getName());
                components.put(componentName, fxmlLoader.load());
                NUIController nuiController;// = new NUIController();
                // before you can get the controller
                // you have to call fxmlLoader.load()
                nuiController = fxmlLoader.getController();
                if (nuiController != null)
                    nuiController.constructor(this, componentName,
                            file.getName());
                controllers.put(componentName, nuiController);

                // create a view position menu for every component
                ToggleGroup toggleGroup = new ToggleGroup();
                toggleGroups.put(componentName, toggleGroup);
                viewPositionMenu.getItems()
                        .add(createSubMenu(componentName, toggleGroup));
            }
        }
    }

    private Menu createSubMenu(String componentName, ToggleGroup toggleGroup) {
        Menu menu = new Menu(componentName);

        String hideText = bundle.getString("hide");
        String leftText = bundle.getString("left");
        String rightText = bundle.getString("right");
        String bottomText = bundle.getString("bottom");
        String middleText = bundle.getString("middle");

        RadioMenuItem hide = new RadioMenuItem(hideText);
        hide.setOnAction(mainViewController.getNewHandleLoadComponent());
        hide.setId("hide");
        hide.getProperties().put("componentResource", componentName + ".fxml");
        hide.getProperties().put("componentName", componentName);
        hide.setToggleGroup(toggleGroup);
        hide.setSelected(true);
        hide.setUserData(Place.HIDDEN);
        menu.getItems().add(hide);

        RadioMenuItem left = new RadioMenuItem(leftText);
        left.setOnAction(mainViewController.getNewHandleLoadComponent());
        left.setId("left");
        left.getProperties().put("componentResource", componentName + ".fxml");
        left.getProperties().put("componentName", componentName);
        left.setToggleGroup(toggleGroup);
        left.setUserData(Place.LEFT);
        menu.getItems().add(left);

        RadioMenuItem right = new RadioMenuItem(rightText);
        right.setOnAction(mainViewController.getNewHandleLoadComponent());
        right.setId("right");
        right.getProperties().put("componentResource", componentName + ".fxml");
        right.getProperties().put("componentName", componentName);
        right.setToggleGroup(toggleGroup);
        right.setUserData(Place.RIGHT);
        menu.getItems().add(right);

        RadioMenuItem bottom = new RadioMenuItem(bottomText);
        bottom.setOnAction(mainViewController.getNewHandleLoadComponent());
        bottom.setId("bottom");
        bottom.getProperties().put("componentResource",
                componentName + ".fxml");
        bottom.getProperties().put("componentName", componentName);
        bottom.setToggleGroup(toggleGroup);
        bottom.setUserData(Place.BOTTOM);
        menu.getItems().add(bottom);

        RadioMenuItem middle = new RadioMenuItem(middleText);
        middle.setOnAction(mainViewController.getNewHandleLoadComponent());
        middle.setId("middle");
        middle.getProperties().put("componentResource",
                componentName + ".fxml");
        middle.getProperties().put("componentName", componentName);
        middle.setToggleGroup(toggleGroup);
        middle.setUserData(Place.MIDDLE);
        menu.getItems().add(middle);

        return menu;
    }

    public Pane getComponent(String name) throws ComponentNotFoundException {
        if (!components.containsKey(name))
            throw new ComponentNotFoundException(name);
        return components.get(name);
    }

    public NUIController getController(String name)
            throws ControllerNotFoundException {
        if (!controllers.containsKey(name))
            throw new ControllerNotFoundException(name);
        return controllers.get(name);
    }

    public ToggleGroup getToggleGroup(String name)
            throws ToggleGroupNotFoundException {
        if (!toggleGroups.containsKey(name))
            throw new ToggleGroupNotFoundException(name);
        return toggleGroups.get(name);
    }

    private String cutFileExtension(String filename) {
        return filename.substring(0, filename.lastIndexOf("."));
    }

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

    public DataModel getDataModel() {
        return dataModel;
    }
}
