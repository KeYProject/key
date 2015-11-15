package de.uka.ilkd.key.nui;

import java.io.IOException;
import java.util.HashMap;

import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.layout.Pane;

public class ComponentFactory {

	private String resourceDir;

	public ComponentFactory(String resourceDir) {
		this.resourceDir = resourceDir;
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
			component = FXMLLoader.load(getClass().getResource(this.resourceDir + resource));
			component.setId(id);
			posComponent.put(id, pane);
			pane.getChildren().add(component);
		} catch (IOException e) {
			e.printStackTrace();
		}
		return component;
	}
}
