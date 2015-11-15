package de.uka.ilkd.key.nui;

import java.io.IOException;
import java.util.HashMap;

import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.layout.Pane;

public class ComponentFactory {

	private String resource;

	public ComponentFactory(String resource) {
		this.resource = resource;
	}

	public ComponentFactory() {
	}

	public Parent createTreeView(String id, Pane pane, HashMap<String, Pane> posComponent) {
		Parent textEditor = createComponent(id, pane, "treeView.fxml", posComponent);
		return textEditor;
	}

	public Parent createTextEditor(String id, Pane pane, HashMap<String, Pane> posComponent) {
		Parent textEditor = createComponent(id, pane, "textEditor.fxml", posComponent);
		return textEditor;
	}

	public Parent createComponent(String id, Pane pane, String resource, HashMap<String, Pane> posComponent) {
		Parent component = null;
		try {
			component = FXMLLoader.load(getClass().getResource("components/" + resource));
			component.setId(id);
			posComponent.put(id, pane);
			pane.getChildren().add(component);
		} catch (IOException e) {
			e.printStackTrace();
		}
		return component;
	}
}
