/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.dialogs;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.collections.transformation.FilteredList;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ListView;
import javafx.scene.control.TextField;
import javafx.scene.control.TitledPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

/**
 * lemma (P2b, A2): JavaFX port of the Swing {@code ItemChooser} (key.ui
 * lemmatagenerator/ItemChooser.java, 497 lines) — the dual-list chooser of the taclet selection
 * dialog: a "Choice" list on the left, a "Selection" list on the right and move buttons in
 * between; both lists work on the same items, each showing the items of its side, filtered by
 * the user filters and the live search pattern of the panel's own text field, sorted by the
 * item's lower-case name (Swing TableRowSorter, ItemChooser.java:411-427).
 *
 * @param <T> the item data type (Swing generic {@code ItemChooser<T>})
 */
public class ItemChooserF<T> extends HBox {

    /** The two sides of the chooser (Swing {@code SelectionPanel.Side}). */
    public enum Side {
        LEFT, RIGHT
    }

    /** Swing {@code ItemChooser.ItemFilter}. */
    public interface ItemFilter<T> {
        boolean include(T itemData);
    }

    /** Swing {@code TableItem<T>}: the item data plus its side and search name. */
    public static final class TableItemF<T> {
        private final T data;
        private final String lowerCaseName;
        private final ObjectProperty<Side> side = new SimpleObjectProperty<>(Side.LEFT);

        public TableItemF(T data, Side side) {
            this.data = data;
            this.side.set(side);
            this.lowerCaseName = data.toString().toLowerCase();
        }

        public T getData() {
            return data;
        }

        public Side getSide() {
            return side.get();
        }

        public void setSide(Side side) {
            this.side.set(side);
        }

        public ObjectProperty<Side> sideProperty() {
            return side;
        }

        public String getNameLowerCase() {
            return lowerCaseName;
        }

        @Override
        public String toString() {
            return data.toString();
        }
    }

    private final String searchTitle;
    private List<TableItemF<T>> items = new LinkedList<>();
    private final List<ItemFilter<T>> filtersForMovingItems = new LinkedList<>();
    private final List<ItemFilter<T>> userFilter = new ArrayList<>();

    private final ObservableList<TableItemF<T>> observableItems =
        FXCollections.observableArrayList();
    private final FilteredList<TableItemF<T>> leftItems =
        new FilteredList<>(observableItems);
    private final FilteredList<TableItemF<T>> rightItems =
        new FilteredList<>(observableItems);
    private final ListView<TableItemF<T>> suppliedList = new ListView<>(leftItems);
    private final ListView<TableItemF<T>> selectedList = new ListView<>(rightItems);

    /**
     * Swing constructor ({@code searchTitle} = the titled border of the search fields,
     * ItemChooser.java:69-72).
     *
     * @param searchTitle the search field title
     */
    public ItemChooserF(String searchTitle) {
        this.searchTitle = searchTitle;
        getStyleClass().add("item-chooser");
        setSpacing(6);
        setPadding(new Insets(4));
        setAlignment(Pos.CENTER);

        TextField leftSearch = new TextField();
        leftSearch.textProperty().addListener((obs, o, n) -> {
            suppliedList.getProperties().put("search", n);
            update();
        });
        TextField rightSearch = new TextField();
        rightSearch.textProperty().addListener((obs, o, n) -> {
            selectedList.getProperties().put("search", n);
            update();
        });

        VBox leftBox = new VBox(4, new Label(searchTitle), leftSearch, suppliedList);
        VBox.setVgrow(suppliedList, Priority.ALWAYS);
        TitledPane leftPane = new TitledPane("Choice", leftBox);
        leftPane.setCollapsible(false);
        HBox.setHgrow(leftPane, Priority.ALWAYS);

        Button leftButton = new Button("<<");
        leftButton.setTooltip(new javafx.scene.control.Tooltip("Remove selection"));
        leftButton.setOnAction(e -> cut(Side.LEFT));
        Button rightButton = new Button(">>");
        rightButton.setTooltip(new javafx.scene.control.Tooltip("Add selection"));
        rightButton.setOnAction(e -> cut(Side.RIGHT));
        VBox middle = new VBox(4, leftButton, rightButton);
        middle.setAlignment(Pos.CENTER);
        middle.getStyleClass().add("item-chooser-middle");

        VBox rightBox = new VBox(4, new Label(searchTitle), rightSearch, selectedList);
        VBox.setVgrow(selectedList, Priority.ALWAYS);
        TitledPane rightPane = new TitledPane("Selection", rightBox);
        rightPane.setCollapsible(false);
        HBox.setHgrow(rightPane, Priority.ALWAYS);

        getChildren().addAll(leftPane, middle, rightPane);

        // the sort of the Swing sorter (by lower-case name, ItemChooser.java:425-426) plus the
        // per-side, filter and search inclusion (Swing RowFilter, ItemChooser.java:380-408)
        leftItems.setPredicate(item -> include(item, Side.LEFT, leftSearch.getText()));
        rightItems.setPredicate(item -> include(item, Side.RIGHT, rightSearch.getText()));

        suppliedList.setCellFactory(view -> new javafx.scene.control.ListCell<>() {
            @Override
            protected void updateItem(TableItemF<T> item, boolean empty) {
                super.updateItem(item, empty);
                setText(empty || item == null ? null : item.toString());
            }
        });
        selectedList.setCellFactory(view -> new javafx.scene.control.ListCell<>() {
            @Override
            protected void updateItem(TableItemF<T> item, boolean empty) {
                super.updateItem(item, empty);
                setText(empty || item == null ? null : item.toString());
            }
        });
    }

    /** Swing RowFilter.include (ItemChooser.java:380-408) for one side. */
    private boolean include(TableItemF<T> item, Side side, String findPattern) {
        for (ItemFilter<T> filter : userFilter) {
            if (!filter.include(item.getData())) {
                return false;
            }
        }
        String pattern = findPattern.toLowerCase();
        if (!pattern.isEmpty() && !item.getNameLowerCase().contains(pattern)) {
            return false;
        }
        return item.getSide() == side;
    }

    /** Swing {@code cut} (ItemChooser.java:124-143): moves the selected items to {@code side}. */
    private void cut(Side side) {
        List<TableItemF<T>> source = side == Side.LEFT ? rightItems : leftItems;
        List<TableItemF<T>> tableItems = new ArrayList<>(source);
        for (TableItemF<T> item : tableItems) {
            boolean move = true;
            for (ItemFilter<T> filter : filtersForMovingItems) {
                if (!filter.include(item.getData())) {
                    move = false;
                }
            }
            if (move) {
                item.setSide(side);
            }
        }
        update();
    }

    /** Swing {@code setItems} (ItemChooser.java:161-180): all items start on the LEFT. */
    public void setItems(List<T> dataForItems, String columnName) {
        items = new LinkedList<>();
        for (T info : dataForItems) {
            items.add(new TableItemF<>(info, Side.LEFT));
        }
        observableItems.setAll(items);
        // Swing sorts by the lower-case name; sorted here by re-setting the filtered lists
        observableItems.sort((a, b) -> a.getNameLowerCase().compareTo(b.getNameLowerCase()));
        update();
        // Swing: getSuppliedList().selectAll()
        suppliedList.getSelectionModel().clearSelection();
        if (!leftItems.isEmpty()) {
            suppliedList.getSelectionModel().selectRange(0, leftItems.size());
        }
    }

    /** Swing {@code getDataOfSelectedItems} (ItemChooser.java:184-193). */
    public List<T> getDataOfSelectedItems() {
        List<T> list = new LinkedList<>();
        for (TableItemF<T> item : items) {
            if (item.getSide() == Side.RIGHT) {
                list.add(item.getData());
            }
        }
        return list;
    }

    /** Swing {@code moveAllToLeft} (ItemChooser.java:195-200). */
    public void moveAllToLeft() {
        for (TableItemF<T> item : items) {
            item.setSide(Side.LEFT);
        }
        update();
    }

    /** Swing {@code moveAllToRight} (ItemChooser.java:202-207). */
    public void moveAllToRight() {
        for (TableItemF<T> item : items) {
            item.setSide(Side.RIGHT);
        }
        update();
    }

    /** Swing {@code removeSelection} (ItemChooser.java:209-212). */
    public void removeSelection() {
        selectedList.getSelectionModel().clearSelection();
        suppliedList.getSelectionModel().clearSelection();
    }

    /** Swing {@code addFilter} (ItemChooser.java:214-217). */
    public void addFilter(ItemFilter<T> filter) {
        userFilter.add(filter);
        update();
    }

    /** Swing {@code removeFilter} (ItemChooser.java:219-222). */
    public void removeFilter(ItemFilter<T> filter) {
        userFilter.remove(filter);
        update();
    }

    /** Swing {@code addFilterForMovingItems} (ItemChooser.java:224-226). */
    public void addFilterForMovingItems(ItemFilter<T> filter) {
        filtersForMovingItems.add(filter);
    }

    /** Swing {@code removeFilterForMovingItems} (ItemChooser.java:228-231). */
    public void removeFilterForMovingItems(ItemFilter<T> filter) {
        filtersForMovingItems.remove(filter);
    }

    /**
     * Swing {@code update} (ItemChooser.java:233-240): re-applies the row filters (the search
     * patterns are re-read from the panels' text fields inside {@link #include}).
     */
    public void update() {
        leftItems.setPredicate(item -> include(item, Side.LEFT, searchOf(suppliedList)));
        rightItems.setPredicate(item -> include(item, Side.RIGHT, searchOf(selectedList)));
    }

    /**
     * The search pattern of the given panel (the Swing {@code findPattern} of the panel's text
     * field). The FX lists carry the pattern in their user data.
     */
    private String searchOf(ListView<TableItemF<T>> list) {
        Object pattern = list.getProperties().get("search");
        return pattern instanceof String s ? s : "";
    }

    /** The {@code searchTitle} (used by the dialog layout). */
    public String getSearchTitle() {
        return searchTitle;
    }
}
