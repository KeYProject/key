/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.drawer;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

import javafx.beans.property.BooleanProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.geometry.Bounds;
import javafx.geometry.Orientation;
import javafx.geometry.Side;
import javafx.scene.Group;
import javafx.scene.Node;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.control.ToggleButton;
import javafx.scene.control.ToolBar;
import javafx.scene.input.ClipboardContent;
import javafx.scene.input.DataFormat;
import javafx.scene.input.DragEvent;
import javafx.scene.input.Dragboard;
import javafx.scene.input.MouseEvent;
import javafx.scene.input.TransferMode;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.Pane;

/**
 * A drawer is a dockable navigation area similar to a {@link javafx.scene.control.TabPane}, but
 * organises its entries — {@link DrawerItemF} — as toggle buttons in a button bar placed on one
 * of the four sides ({@link javafx.geometry.Side} {@code LEFT/RIGHT/TOP/BOTTOM}). Expanding an
 * item shows its content in the content area next to the button bar. In multiselect mode several
 * items can be expanded simultaneously; their contents share the content area, each growing
 * equally (the "split pane" behaviour) and always in the order of the corresponding buttons.
 * In exclusive mode expanding one item collapses all others.
 *
 * <p>
 * Faithful Java port of TornadoFX {@code Drawer} (Kotlin:
 * {@code tornadofx/Drawer.kt}, guide sections "Drawer" and "Drawer multiselect"), with two
 * features added on top:
 * <ul>
 * <li><b>Drag and drop reordering</b> — a toggle button can be dragged within the button bar to
 * change its position; the item order determines both the button order and the order of the
 * expanded contents in the content area.</li>
 * <li><b>Drag and drop transfer</b> — a toggle button can be dragged onto another drawer (a
 * different <i>port</i>, e.g. the east drawer instead of the west drawer) to move the item,
 * including its expanded state, to that drawer.</li>
 * </ul>
 *
 * <p>
 * Documented deviations from the Kotlin original: the content area is a plain {@code VBox} with
 * equal vertical growth (as in the original — not a divider-based SplitPane); the context menu
 * exposes the original's "Floating drawers" and "Multiselect" entry; titles are plain
 * {@link String}s (no {@code ObservableValue} binding).
 */
public class DrawerF extends BorderPane {

    // ------------------------------------------------------------------ drag and drop

    /** Dragboard format used to move drawer items between and within drawers. */
    public static final DataFormat DRAWER_ITEM_FORMAT =
        new DataFormat("application/x-keyfx-draweritem");

    private static final Map<String, DrawerF> DRAWERS = new ConcurrentHashMap<>();
    private static final Map<String, DrawerItemF> ITEMS = new ConcurrentHashMap<>();
    private static final AtomicInteger DRAWER_IDS = new AtomicInteger();
    private static final AtomicInteger ITEM_IDS = new AtomicInteger();

    static String keyOf(DrawerItemF item) {
        return item.getDrawer().id + "#" + item.getItemId();
    }

    static long nextItemId() {
        return ITEM_IDS.incrementAndGet();
    }

    static void register(DrawerItemF item) {
        ITEMS.put(keyOf(item), item);
    }

    // ------------------------------------------------------------------ properties (TornadoFX
    // port)

    private final ObjectProperty<Side> dockingSideProperty =
        new SimpleObjectProperty<>(Side.LEFT);
    private final BooleanProperty floatingDrawersProperty = new SimpleBooleanProperty(false);
    private final ObjectProperty<Number> maxContentSizeProperty = new SimpleObjectProperty<>();
    private final ObjectProperty<Number> fixedContentSizeProperty = new SimpleObjectProperty<>();
    private final BooleanProperty multiselectProperty = new SimpleBooleanProperty(false);

    // ------------------------------------------------------------------ parts

    private final String id;
    private final ToolBar buttonArea = new ToolBar();
    private final DrawerContentAreaF contentArea = new DrawerContentAreaF();
    private final ObservableList<DrawerItemF> items = FXCollections.observableArrayList();
    private final ContextMenu contextMenu = new ContextMenu();

    // drag-and-drop visual cue state
    private Node indicatedNode;
    private String indicatedStyle;

    public DrawerF() {
        this(Side.LEFT, false, false);
    }

    public DrawerF(Side side) {
        this(side, false, false);
    }

    public DrawerF(Side side, boolean multiselect) {
        this(side, multiselect, false);
    }

    public DrawerF(Side side, boolean multiselect, boolean floatingDrawers) {
        this.id = "drawer-" + DRAWER_IDS.incrementAndGet();
        DRAWERS.put(id, this);
        dockingSideProperty.set(side);
        multiselectProperty.set(multiselect);
        floatingDrawersProperty.set(floatingDrawers);
        buttonArea.setStyle("-fx-spacing: 0; -fx-padding: 0;");

        configureDockingSide();
        configureContextMenu();
        enforceMultiSelect();

        // adapt the docking side to the slot in the parent BorderPane
        parentProperty().addListener((obs, oldParent, parent) -> {
            if (parent instanceof BorderPane bp) {
                if (bp.getLeft() == this) {
                    setDockingSide(Side.LEFT);
                } else if (bp.getRight() == this) {
                    setDockingSide(Side.RIGHT);
                } else if (bp.getBottom() == this) {
                    setDockingSide(Side.BOTTOM);
                } else if (bp.getTop() == this) {
                    setDockingSide(Side.TOP);
                }
            }
        });
        dockingSideProperty.addListener((obs, oldSide, newSide) -> configureDockingSide());
        floatingDrawersProperty.addListener((obs, oldValue, newValue) -> {
            updateContentArea();
            requestLayout();
            if (getScene() != null && getScene().getRoot() != null) {
                getScene().getRoot().requestLayout();
            }
        });

        // maintain the button bar and the content area when items are added or removed
        items.addListener((ListChangeListener<DrawerItemF>) change -> {
            while (change.next()) {
                if (change.wasAdded()) {
                    for (DrawerItemF item : change.getAddedSubList()) {
                        item.getButton().setOnDragDetected(
                            e -> onDragDetected(item, e));
                        installDropTargets(item);
                        buttonArea.getItems().add(new Group(item.getButton()));
                        configureRotation(item.getButton());
                    }
                }
                if (change.wasRemoved()) {
                    for (DrawerItemF item : change.getRemoved()) {
                        detachButton(item);
                    }
                }
            }
        });
    }

    /** Removes the item's button from the bar (button, its group and its drag handlers). */
    private void detachButton(DrawerItemF item) {
        Node parent = item.getButton().getParent();
        if (parent instanceof Pane pane) {
            pane.getChildren().remove(item.getButton());
        }
        if (parent != null) {
            buttonArea.getItems().remove(parent);
        }
        item.getButton().setOnDragDetected(null);
        item.getButton().setOnDragOver(null);
        item.getButton().setOnDragDropped(null);
        item.getButton().setOnDragDone(null);
    }

    // ------------------------------------------------------------------ TornadoFX builder API

    /** Creates a new collapsed item with the given title. */
    public DrawerItemF item(String title) {
        return item(title, (Node) null, false);
    }

    /** Creates a new collapsed item showing {@code content} when expanded. */
    public DrawerItemF item(String title, Node content) {
        return item(title, content, false);
    }

    /** Creates a new item; {@code expanded} controls the initial state. */
    public DrawerItemF item(String title, boolean expanded) {
        return item(title, null, expanded);
    }

    /**
     * Creates a new item with the given title, optional content and initial expanded state. The
     * header is shown by default when the drawer is in multiselect mode (TornadoFX default).
     */
    public DrawerItemF item(String title, Node content, boolean expanded) {
        DrawerItemF item = new DrawerItemF(this, title, null, isMultiselect());
        if (content != null) {
            item.getChildren().add(content);
        }
        items.add(item);
        if (expanded) {
            item.getButton().setSelected(true);
        }
        return item;
    }

    /** Removes the given item and collapses it first (if expanded). */
    public void removeItem(DrawerItemF item) {
        if (item != null && item.getDrawer() == this) {
            item.getButton().setSelected(false);
            items.remove(item);
        }
    }

    /** Removes all items. */
    public void clearItems() {
        new ArrayList<>(items).forEach(this::removeItem);
    }

    // ------------------------------------------------------------------ state machine (TornadoFX
    // port)

    void updateExpanded(DrawerItemF item) {
        if (item.isExpanded()) {
            if (!contentArea.getChildren().contains(item)) {
                if (!isMultiselect()) {
                    for (Node child : contentArea.getChildren().toArray(new Node[0])) {
                        ((DrawerItemF) child).getButton().setSelected(false);
                    }
                }
                // insert into the content area in the order of the buttons
                int itemIndex = items.indexOf(item);
                boolean inserted = false;
                for (int i = 0; i < contentArea.getChildren().size(); i++) {
                    DrawerItemF child = (DrawerItemF) contentArea.getChildren().get(i);
                    if (items.indexOf(child) > itemIndex) {
                        contentArea.getChildren().add(i, item);
                        inserted = true;
                        break;
                    }
                }
                if (!inserted) {
                    contentArea.getChildren().add(item);
                }
            }
        } else {
            contentArea.getChildren().remove(item);
        }
        updateContentArea();
    }

    private void updateContentArea() {
        if (contentArea.getChildren().isEmpty()) {
            setCenter(null);
            getChildren().remove(contentArea);
        } else {
            Number fixed = fixedContentSizeProperty.get();
            if (fixed != null) {
                double size = fixed.doubleValue();
                if (getDockingSide() == Side.LEFT || getDockingSide() == Side.RIGHT) {
                    contentArea.setMaxWidth(size);
                    contentArea.setMinWidth(size);
                } else {
                    contentArea.setMaxHeight(size);
                    contentArea.setMinHeight(size);
                }
            } else {
                contentArea.setMaxWidth(USE_COMPUTED_SIZE);
                contentArea.setMinWidth(USE_COMPUTED_SIZE);
                contentArea.setMaxHeight(USE_COMPUTED_SIZE);
                contentArea.setMinHeight(USE_COMPUTED_SIZE);
                Number max = maxContentSizeProperty.get();
                if (max != null) {
                    if (getDockingSide() == Side.LEFT || getDockingSide() == Side.RIGHT) {
                        contentArea.setMaxWidth(max.doubleValue());
                    } else {
                        contentArea.setMaxHeight(max.doubleValue());
                    }
                }
            }

            if (isFloatingDrawers()) {
                contentArea.setManaged(false);
                if (!getChildren().contains(contentArea)) {
                    getChildren().add(contentArea);
                }
            } else {
                contentArea.setManaged(true);
                getChildren().remove(contentArea);
                setCenter(contentArea);
            }
        }
    }

    private void configureRotation(ToggleButton button) {
        button.setRotate(switch (getDockingSide()) {
            case LEFT -> -90.0;
            case RIGHT -> 90.0;
            default -> 0.0;
        });
    }

    private void configureDockingSide() {
        switch (getDockingSide()) {
            case LEFT -> {
                setLeft(buttonArea);
                setRight(null);
                setBottom(null);
                setTop(null);
                buttonArea.setOrientation(Orientation.VERTICAL);
            }
            case RIGHT -> {
                setLeft(null);
                setRight(buttonArea);
                setBottom(null);
                setTop(null);
                buttonArea.setOrientation(Orientation.VERTICAL);
            }
            case BOTTOM -> {
                setLeft(null);
                setRight(null);
                setBottom(buttonArea);
                setTop(null);
                buttonArea.setOrientation(Orientation.HORIZONTAL);
            }
            case TOP -> {
                setLeft(null);
                setRight(null);
                setBottom(null);
                setTop(buttonArea);
                buttonArea.setOrientation(Orientation.HORIZONTAL);
            }
        }
        for (Node node : buttonArea.getItems()) {
            if (node instanceof Group group && !group.getChildren().isEmpty()
                    && group.getChildren().get(0) instanceof ToggleButton button) {
                configureRotation(button);
            }
        }
    }

    /** In exclusive mode expanding an item collapses the remaining expanded items. */
    private void enforceMultiSelect() {
        multiselectProperty.addListener((obs, oldValue, newValue) -> {
            if (!newValue) {
                for (int i = 1; i < contentArea.getChildren().size(); i++) {
                    ((DrawerItemF) contentArea.getChildren().get(i)).getButton()
                            .setSelected(false);
                }
            }
        });
    }

    private void configureContextMenu() {
        CheckMenuItem floating = new CheckMenuItem("Floating drawers");
        floating.selectedProperty().bindBidirectional(floatingDrawersProperty);
        CheckMenuItem multiselect = new CheckMenuItem("Multiselect");
        multiselect.selectedProperty().bindBidirectional(multiselectProperty);
        contextMenu.getItems().addAll(floating, multiselect);
        buttonArea.setOnContextMenuRequested(
            event -> contextMenu.show(buttonArea, event.getScreenX(), event.getScreenY()));
    }

    /** Floating drawers overlay the content area next to the button bar. */
    @Override
    protected void layoutChildren() {
        super.layoutChildren();
        if (isFloatingDrawers() && !contentArea.getChildren().isEmpty()) {
            Bounds buttonBounds = buttonArea.getLayoutBounds();
            if (getDockingSide() == Side.RIGHT) {
                contentArea.resizeRelocate(
                    buttonBounds.getMinX() - contentArea.prefWidth(-1),
                    buttonBounds.getMinY(),
                    contentArea.prefWidth(-1),
                    buttonBounds.getHeight());
            } else {
                contentArea.resizeRelocate(
                    buttonBounds.getMaxX(),
                    buttonBounds.getMinY(),
                    contentArea.prefWidth(-1),
                    buttonBounds.getHeight());
            }
        }
    }

    // ------------------------------------------------------------------ drag and drop (reorder +
    // transfer)

    private void onDragDetected(DrawerItemF item, MouseEvent event) {
        if (item.getDrawer() != this) {
            return;
        }
        Dragboard dragboard = item.getButton().startDragAndDrop(TransferMode.MOVE);
        ClipboardContent content = new ClipboardContent();
        content.put(DRAWER_ITEM_FORMAT, keyOf(item));
        dragboard.setContent(content);
        event.consume();
    }

    /** Makes the button and the bar drop targets for items dragged from any drawer. */
    private void installDropTargets(DrawerItemF item) {
        ToggleButton button = item.getButton();
        button.setOnDragOver(e -> onDragOver(e));
        button.setOnDragDropped(e -> onDragDropped(e, this));
        button.setOnDragDone(e -> clearIndication());
        buttonArea.setOnDragOver(e -> onDragOver(e));
        buttonArea.setOnDragDropped(e -> onDragDropped(e, this));
        buttonArea.setOnDragDone(e -> clearIndication());
    }

    private void onDragOver(DragEvent event) {
        Dragboard dragboard = event.getDragboard();
        if (dragboard.hasContent(DRAWER_ITEM_FORMAT)) {
            event.acceptTransferModes(TransferMode.MOVE);
            indicate(insertionIndexAtScene(event.getSceneX(), event.getSceneY()));
        }
        event.consume();
    }

    private void onDragDropped(DragEvent event, DrawerF targetDrawer) {
        Dragboard dragboard = event.getDragboard();
        boolean completed = false;
        if (dragboard.hasContent(DRAWER_ITEM_FORMAT)) {
            DrawerItemF source =
                ITEMS.get(String.valueOf(dragboard.getContent(DRAWER_ITEM_FORMAT)));
            if (source != null) {
                DrawerF sourceDrawer = source.getDrawer();
                if (sourceDrawer == targetDrawer) {
                    // reorder within the same drawer
                    targetDrawer.moveItem(sourceDrawer.items.indexOf(source),
                        targetDrawer.insertionIndexAtScene(event.getSceneX(), event.getSceneY()));
                } else {
                    // transfer to a different port
                    sourceDrawer.transferItem(source, targetDrawer);
                }
                completed = true;
            }
        }
        event.setDropCompleted(completed);
        clearIndication();
        event.consume();
    }

    /**
     * Computes the insertion index for a drop at the given scene coordinates: the index of the
     * first button whose centre lies beyond the drop point (vertical bars compare y, horizontal
     * bars compare x); a drop behind the last button appends.
     */
    private int insertionIndexAtScene(double sceneX, double sceneY) {
        boolean vertical = buttonArea.getOrientation() == Orientation.VERTICAL;
        for (int i = 0; i < items.size(); i++) {
            Node button = items.get(i).getButton();
            Bounds bounds = button.localToScene(button.getBoundsInLocal());
            double centre = vertical
                    ? (bounds.getMinY() + bounds.getMaxY()) / 2
                    : (bounds.getMinX() + bounds.getMaxX()) / 2;
            double dropPoint = vertical ? sceneY : sceneX;
            if (dropPoint < centre) {
                return i;
            }
        }
        return items.size();
    }

    private void indicate(int index) {
        if (index >= 0 && index < items.size()) {
            Node node = items.get(index).getButton();
            if (node != indicatedNode) {
                clearIndication();
                indicatedNode = node;
                indicatedStyle = node.getStyle();
                node.setStyle((indicatedStyle.isEmpty() ? "" : indicatedStyle + ";")
                    + "-fx-border-color: #4a90d9; -fx-border-width: 2;");
            }
        }
    }

    private void clearIndication() {
        if (indicatedNode != null) {
            indicatedNode.setStyle(indicatedStyle == null ? "" : indicatedStyle);
            indicatedNode = null;
            indicatedStyle = null;
        }
    }

    /**
     * Moves the item at {@code fromIndex} to {@code toIndex} within this drawer. The item order
     * determines both the button-bar order and the order of the expanded contents in the content
     * area.
     */
    public void moveItem(int fromIndex, int toIndex) {
        if (fromIndex < 0 || fromIndex >= items.size() || fromIndex == toIndex) {
            return;
        }
        if (toIndex < 0) {
            toIndex = 0;
        }
        if (toIndex >= items.size()) {
            toIndex = items.size() - 1;
        }
        DrawerItemF moved = items.remove(fromIndex);
        items.add(toIndex, moved);
        rebuildButtonBar();
        resyncContentOrder();
    }

    /**
     * Moves {@code item} from this drawer to {@code target} (a different port). The expanded
     * state is preserved; the item appears at the end of the target's button bar.
     */
    public void transferItem(DrawerItemF item, DrawerF target) {
        if (item == null || target == null || item.getDrawer() == target) {
            return;
        }
        DrawerF source = item.getDrawer();
        boolean expanded = item.getButton().isSelected();
        item.getButton().setSelected(false);
        source.items.remove(item);
        ITEMS.remove(keyOf(item));
        item.setDrawer(target);
        target.items.add(item);
        ITEMS.put(keyOf(item), item);
        if (expanded) {
            item.getButton().setSelected(true);
        }
    }

    /** Rebuilds the button bar in the current item order (used after a reordering move). */
    private void rebuildButtonBar() {
        buttonArea.getItems().clear();
        for (DrawerItemF item : items) {
            buttonArea.getItems().add(new Group(item.getButton()));
            configureRotation(item.getButton());
        }
    }

    /** Re-inserts the expanded items into the content area following the button order. */
    private void resyncContentOrder() {
        List<DrawerItemF> expanded = new ArrayList<>();
        for (DrawerItemF item : items) {
            if (item.isExpanded() && contentArea.getChildren().contains(item)) {
                expanded.add(item);
            }
        }
        if (expanded.size() == contentArea.getChildren().size()) {
            contentArea.getChildren().setAll(expanded);
        }
    }

    // ------------------------------------------------------------------ accessors

    public ObjectProperty<Side> dockingSideProperty() {
        return dockingSideProperty;
    }

    public Side getDockingSide() {
        return dockingSideProperty.get();
    }

    public void setDockingSide(Side side) {
        dockingSideProperty.set(side);
    }

    public BooleanProperty floatingDrawersProperty() {
        return floatingDrawersProperty;
    }

    public boolean isFloatingDrawers() {
        return floatingDrawersProperty.get();
    }

    public void setFloatingDrawers(boolean floating) {
        floatingDrawersProperty.set(floating);
    }

    public ObjectProperty<Number> maxContentSizeProperty() {
        return maxContentSizeProperty;
    }

    public Number getMaxContentSize() {
        return maxContentSizeProperty.get();
    }

    public void setMaxContentSize(Number size) {
        maxContentSizeProperty.set(size);
    }

    public ObjectProperty<Number> fixedContentSizeProperty() {
        return fixedContentSizeProperty;
    }

    public Number getFixedContentSize() {
        return fixedContentSizeProperty.get();
    }

    public void setFixedContentSize(Number size) {
        fixedContentSizeProperty.set(size);
    }

    public BooleanProperty multiselectProperty() {
        return multiselectProperty;
    }

    public boolean isMultiselect() {
        return multiselectProperty.get();
    }

    public void setMultiselect(boolean multiselect) {
        multiselectProperty.set(multiselect);
    }

    public ToolBar getButtonArea() {
        return buttonArea;
    }

    public DrawerContentAreaF getContentArea() {
        return contentArea;
    }

    public ObservableList<DrawerItemF> getItems() {
        return items;
    }

    public ContextMenu getContextMenu() {
        return contextMenu;
    }

    /** @return the stable identifier used in the drag-and-drop registry */
    public String getDrawerId() {
        return id;
    }

    // ------------------------------------------------------------------ self test
    // (key.fx.verify.drawer)

    /**
     * Headless self test exercising exclusive/multiselect semantics, side placement, the button
     * order in the content area, reordering and cross-drawer transfer — the same methods the
     * drag-and-drop handlers invoke. No {@code Scene} is required. Called by the
     * {@code key.fx.verify.drawer} verification hook.
     *
     * @return a single-line PASS/FAIL report
     */
    public static String selfTest() {
        List<String> checks = new ArrayList<>();
        try {
            // exclusive mode: expanding one item collapses the others
            DrawerF d = new DrawerF(Side.LEFT, false);
            DrawerItemF a = d.item("A");
            DrawerItemF b = d.item("B");
            d.item("C");
            a.getButton().setSelected(true);
            b.getButton().setSelected(true);
            checks.add("exclusive=" + (d.getContentArea().getChildren().size() == 1
                    && d.getContentArea().getChildren().contains(b) ? "PASS" : "FAIL"));

            // side placement and bar orientation
            d.setDockingSide(Side.RIGHT);
            checks.add("sideRight=" + (d.getRight() == d.getButtonArea()
                    && d.buttonArea.getOrientation() == Orientation.VERTICAL ? "PASS" : "FAIL"));
            d.setDockingSide(Side.BOTTOM);
            checks.add("sideBottom=" + (d.getBottom() == d.getButtonArea()
                    && d.buttonArea.getOrientation() == Orientation.HORIZONTAL ? "PASS" : "FAIL"));
            checks.add("centerHost=" + (d.getCenter() == d.getContentArea() ? "PASS" : "FAIL"));

            // multiselect: two expanded items share the content area in button order + header
            DrawerF m = new DrawerF(Side.LEFT, true);
            m.item("A", new Label("a-content"), true);
            m.item("B", new Label("b-content"));
            DrawerItemF mB = m.item("C", new Label("c-content"));
            mB.getButton().setSelected(true);
            checks.add("multiOrder=" + (m.getContentArea().getChildren().size() == 2
                    && m.getContentArea().getChildren().get(0) == m.getItems().get(0)
                    && m.getContentArea().getChildren().get(1) == mB ? "PASS" : "FAIL"));
            checks.add("multiHeader=" + (mB.getHeader() != null ? "PASS" : "FAIL"));

            // reorder: move item 1 (B) to the bar front; bar and content follow the new order
            // after the move: items = [B, A, C]
            m.moveItem(1, 0);
            Group bar0 = (Group) m.getButtonArea().getItems().get(0);
            Group bar2 = (Group) m.getButtonArea().getItems().get(2);
            checks.add("reorder=" + (m.getItems().get(0).getButton().getText().equals("B")
                    && bar0.getChildren().get(0) == m.getItems().get(0).getButton()
                    && bar2.getChildren().get(0) == mB.getButton()
                    && m.getContentArea().getChildren().get(0) == m.getItems().get(1)
                    && m.getContentArea().getChildren().get(1) == m.getItems().get(2)
                            ? "PASS"
                            : "FAIL"));

            // switching multiselect off collapses all but the first expanded item
            m.setMultiselect(false);
            checks.add("collapse=" + (m.getContentArea().getChildren().size() == 1 ? "PASS"
                    : "FAIL"));

            // transfer to a different drawer (different port)
            DrawerF t = new DrawerF(Side.RIGHT, true);
            m.transferItem(m.getItems().get(1), t);
            checks.add("transfer=" + (m.getItems().size() == 2 && t.getItems().size() == 1
                    && t.getContentArea().getChildren().contains(t.getItems().get(0))
                    && t.getItems().get(0).isExpanded() ? "PASS" : "FAIL"));
        } catch (RuntimeException ex) {
            checks.add("EXCEPTION=" + ex);
        }
        boolean pass = checks.stream().allMatch(check -> check.endsWith("PASS"));
        return (pass ? "PASS" : "FAIL") + " - " + String.join(" ", checks);
    }
}
