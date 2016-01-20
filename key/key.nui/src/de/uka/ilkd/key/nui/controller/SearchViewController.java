package de.uka.ilkd.key.nui.controller;

import java.net.URL;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;
import java.util.ResourceBundle;
import java.util.stream.Collectors;

import de.uka.ilkd.key.nui.ComponentFactory;
import de.uka.ilkd.key.nui.prooftree.NUINode;
import de.uka.ilkd.key.nui.prooftree.ProofTreeActions;
import javafx.application.Platform;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.scene.control.Button;
import javafx.scene.control.TextField;
import javafx.scene.control.TreeItem;

public class SearchViewController implements Initializable {

    @FXML
    TextField SearchTextField;
    @FXML
    Button PreviousButton;
    @FXML
    Button NextButton;
    @FXML
    Button SearchButton;

    private List<TreeItem<NUINode>> searchResults;

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        Platform.runLater(new Runnable() {
            @Override
            public void run() {
                SearchTextField.requestFocus();
            }
        });
        SearchTextField.textProperty().addListener(new ChangeListener<String>() {
            @Override
            public void changed(ObservableValue<? extends String> observable, String oldValue,
                    String newValue) {
                SearchButton.setDisable(newValue.isEmpty());
                searchResults = null;
                if (newValue.isEmpty()) {
                    NextButton.setDisable(true);
                    PreviousButton.setDisable(true);
                }
            }
        });
        SearchButton.setDisable(true);
    }

    public void handleSearchButton(ActionEvent e) {

        TreeViewController tVC = ComponentFactory.getInstance().getController("treeView");
        List<TreeItem<NUINode>> searchItemsArray = tVC.getItems();

        if (searchResults != null) {
            for (TreeItem<NUINode> t : searchResults) {
                t.getValue().setHighlighting(false);
            }
        }

        searchResults = new LinkedList<>();

        for (TreeItem<NUINode> t : searchItemsArray) {
            if (t.getValue().getLabel().toLowerCase()
                    .contains(SearchTextField.getText().toLowerCase())) {
                searchResults.add(t);
            }
        }

        if (!searchResults.isEmpty()) {
            for (TreeItem<NUINode> t : searchResults) {
                t.getValue().setHighlighting(true);
                ProofTreeActions.refreshTreeItem(t);
            }
            handleNextButton(e);

            if (!SearchButton.isDisable()) {
                NextButton.setDisable(false);
                PreviousButton.setDisable(false);
            }
        }
    }

    /**
     * TODO implementation may be terrible
     * 
     * @param e
     */
    public void handleNextButton(ActionEvent e) {

        // check if match list is empty
        if (searchResults.isEmpty()) {
            return;
        }

        // the current selected index
        TreeViewController t = ComponentFactory.getInstance().getController("treeView");
        int idxSelected = t.getCurrentlySelectedItemsIndex();

        // get next higher index and its tree node
        // TODO can be very much improved using your grips
        // store list of indices of matches
        List<Integer> idxOfMatches = new LinkedList<>();
        for (TreeItem<NUINode> i : searchResults) {
            int idx = t.getTreeItemsRow(i);
            idxOfMatches.add(idx);
            System.out.print(idx + " ");
        }
        System.out.println();

        // select the next largest match index.
        // if there is no, choose match with smallest index.
        int nextLargerIdx;
        List<Integer> listLargerThanSelected = idxOfMatches.stream().filter(s -> s > idxSelected)
                .collect(Collectors.toList());
        if (!listLargerThanSelected.isEmpty()) {
            // TODO Can be done very much smarter i guess
            nextLargerIdx = listLargerThanSelected.stream().min(Comparator.comparingInt(i -> i))
                    .get();
        }
        else {
            // TODO not the smartest way...
            nextLargerIdx = idxOfMatches.stream().min(Comparator.comparingInt(i -> i)).get();
        }

        // TODO this is very inefficient
        // Problem is that you can't get the TreeItem by index by
        // proofTreeView.getTreeItem(row) if parents of the treeItem
        // are collapsed
        int idxInList = idxOfMatches.indexOf(nextLargerIdx);
        TreeItem<NUINode> nextLargerTI = searchResults.get(idxInList);

        // expand all parents so we can reach the treeItem
        // TODO this is also not very smartly done and could be refactored
        // in a recursive method. However, if you change the lines before
        // this could be superfluous.
        TreeItem<NUINode> parent = nextLargerTI;
        while (parent.getParent() != null) {
            parent = parent.getParent();
            parent.setExpanded(true);
        }

        // scrolling and selecting
        t.scrollToAndSelect(nextLargerIdx);
        System.out
                .println("Currently Selected: " + idxSelected + ", Next Match at " + nextLargerIdx);
    }

    public void handlePreviousButton(ActionEvent e) {
        // TODO
    }

    public void handleEnterKey(ActionEvent e) {
        if (searchResults != null)
            handleNextButton(e);
        else
            handleSearchButton(e);
    }

    public void performFocusRequest() {
        SearchTextField.requestFocus();
    }
}
