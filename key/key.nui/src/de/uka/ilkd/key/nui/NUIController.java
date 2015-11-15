package de.uka.ilkd.key.nui;

import java.util.HashMap;

import javafx.application.Platform;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.Parent;
import javafx.scene.control.Button;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.input.ContextMenuEvent;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;

public class NUIController {

	// Used to determine where component should be placed on
	private Pane lastClicked;

	// Stores the position of components added to the SplitPane
	private HashMap<String, Pane> posComponent = new HashMap<String, Pane>();

	private ComponentFactory componentFactory = new ComponentFactory("");

	// Definition of GUI fields
	@FXML
	VBox left;
	@FXML
	AnchorPane middle;
	@FXML
	VBox right;
	@FXML
	Parent root;
	@FXML
	Label statustext;
	@FXML
	ContextMenu contextMenu;
	@FXML
	CheckMenuItem proof;

	@FXML
	protected void handleLoadContextMenuLeft(ContextMenuEvent event) {
		System.out.println("Load contextmenu left.");
	}

	@FXML
	protected void handleCloseWindow(ActionEvent e) {
		Platform.exit();
	}

	@FXML
	protected void handleAboutWindow(ActionEvent e) {
		System.out.println("Clicked 'About'.");
	}

	@FXML
	protected void handleContextMenu(ActionEvent e) {
		CheckMenuItem clickedEntry = (CheckMenuItem) e.getSource();
		System.out.println(clickedEntry.getId());

		Pane placeOn = null;

		if (lastClicked == left)
			placeOn = left;
		else if (lastClicked == right)
			placeOn = right;
		else if (lastClicked == middle) {
			placeOn = middle;
		}

		// view not added to AnchorPane yet -> add view to AnchorPane
		if (clickedEntry.isSelected()) {
			switch (clickedEntry.getId()) {
			case "proof":
				componentFactory.createTreeView("proof", placeOn, posComponent);
				break;
			case "goals":
				componentFactory.createTextEditor("goals", placeOn, posComponent);
				break;
			case "userConstraints":
				placeOn.getChildren().add(new Button("userConstraints"));
				break;
			case "rules":
				placeOn.getChildren().add(new Button("rules"));
				break;
			case "proofSearchStrategy":
				placeOn.getChildren().add(new Label("proofSearchStrategy"));
				break;
			default:
				break;
			}
		}
		// view already added to AnchorPane -> remove view from AnchorPane
		else {
			switch (clickedEntry.getId()) {
			case "proof":
				System.out.println(placeOn.getChildren().toString());
				posComponent.get(clickedEntry.getId()).getChildren().removeIf(p -> p.getId().equals("proof"));
				break;
			case "goals":
				posComponent.get(clickedEntry.getId()).getChildren().removeIf(p -> p.getId().equals("goals"));
				break;
			case "userConstraints":
				placeOn.getChildren().removeIf(p -> p.toString().contains("userConstraints"));
				break;
			case "rules":
				placeOn.getChildren().removeIf(p -> p.toString().contains("rules"));
				break;
			case "proofSearchStrategy":
				placeOn.getChildren().removeIf(p -> p.toString().contains("proofSearchStrategy"));
				break;
			default:
				break;
			}
		}
	}

	@FXML
	protected void handleLoadGoals(ActionEvent e) {
	}

	@FXML
	protected void handleLoadUserConstraint(ActionEvent e) {
	}

	@FXML
	protected void handleLoadProofSearchStrategy(ActionEvent e) {
	}

	@FXML
	protected void handleLoadRules(ActionEvent e) {
	}

	@FXML
	protected void handleMouseClicked(MouseEvent e) {
		// save information on which AnchorPane the event was triggered
		lastClicked = (Pane) e.getSource();
		System.out.println(lastClicked);
	}

	/**
	 * Initialization method for scene
	 */
	public void initialize() {
	}
}
