/*
 *  Copyright (c) 2016, 2018 Pixel Duke (Pedro Duque Vieira - www.pixelduke.com)
 *  All rights reserved.
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions are met:
 *    * Redistributions of source code must retain the above copyright
 *  notice, this list of conditions and the following disclaimer.
 *    * Redistributions in binary form must reproduce the above copyright
 *  notice, this list of conditions and the following disclaimer in the
 *  documentation and/or other materials provided with the distribution.
 *    * Neither the name of Pixel Duke, any associated website, nor the
 *  names of its contributors may be used to endorse or promote products
 *  derived from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 *  ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 *  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 *  DISCLAIMED. IN NO EVENT SHALL PIXEL DUKE BE LIABLE FOR ANY
 *  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 *  (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 *  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 *  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 *  SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package io.github.wadoon.key.controls

import javafx.beans.property.SimpleObjectProperty
import javafx.beans.value.ObservableValue
import javafx.collections.FXCollections
import javafx.collections.ListChangeListener
import javafx.collections.ObservableList
import javafx.geometry.NodeOrientation
import javafx.geometry.Orientation
import javafx.geometry.Pos
import javafx.scene.Node
import javafx.scene.control.*
import javafx.scene.layout.BorderPane
import javafx.scene.layout.HBox
import javafx.scene.layout.StackPane
import javafx.scene.layout.VBox
import tornadofx.*

class Ribbon : Control() {
    val tabs: ObservableList<RibbonTab?>
    var quickAccessBar: QuickAccessBar
    /***************************************************************************
     * *
     * Properties                                                              *
     * *
     */
    /** Selected Ribbon Tab  */
    internal var selectedRibbonTab = SimpleObjectProperty<RibbonTab>()

    init {
        quickAccessBar = QuickAccessBar()
        tabs = FXCollections.observableArrayList()
        styleClass.setAll(DEFAULT_STYLE_CLASS)
    }

    fun selectedRibbonTabProperty(): SimpleObjectProperty<*> {
        return selectedRibbonTab
    }

    fun getSelectedRibbonTab(): RibbonTab {
        return selectedRibbonTab.get()
    }

    fun setSelectedRibbonTab(ribbonTab: RibbonTab) {
        selectedRibbonTab.set(ribbonTab)
    }

    override fun getUserAgentStylesheet(): String {
        return Ribbon::class.java.getResource("/fxribbon.css").toExternalForm()
    }

    override fun createDefaultSkin(): Skin<*> {
        return RibbonSkin(this)
    }

    companion object {
        private const val DEFAULT_STYLE_CLASS = "ribbon"
    }
}


class Column : VBox() {
    init {
        styleClass.setAll(DEFAULT_STYLE_CLASS)
        alignment = Pos.BASELINE_LEFT
    }

    companion object {
        private const val DEFAULT_STYLE_CLASS = "column"
    }
}


class QuickAccessBar : Control() {
    val buttons: ObservableList<Button>

    //TODO: Clarify this..
    val rightButtons: ObservableList<Button>

    init {
        buttons = FXCollections.observableArrayList()
        rightButtons = FXCollections.observableArrayList()
        styleClass.setAll(DEFAULT_STYLE_CLASS)
    }

    override fun createDefaultSkin(): Skin<*> {
        return QuickAccessBarSkin(this)
    }

    companion object {
        private const val DEFAULT_STYLE_CLASS = "quick-access-bar"
    }
}

class RibbonGroup : Labeled() {
    val nodes: ObservableList<Node?> = FXCollections.observableArrayList()
    //val titleProperty = stringProperty("")
    var title by textProperty()

    init {
        styleClass.setAll(DEFAULT_STYLE_CLASS)
        alignment = Pos.TOP_CENTER
    }

    override fun createDefaultSkin(): Skin<*> {
        return RibbonGroupSkin(this)
    }

    companion object {
        private const val DEFAULT_STYLE_CLASS = "ribbon-group"
    }
}

class RibbonItem : Control() {
    val graphicProperty = objectProperty<Node?>(null)
    var graphic by PropertyDelegate(graphicProperty)
    val labelProperty = stringProperty("")
    var label : String by PropertyDelegate(labelProperty)
    val itemProperty = objectProperty<Node?>()
    var item by PropertyDelegate(itemProperty)

    init {
        styleClass.setAll(DEFAULT_STYLE_CLASS)
    }

    override fun createDefaultSkin(): Skin<*> {
        return RibbonItemSkin(this)
    }

    companion object {
        private const val DEFAULT_STYLE_CLASS = "ribbon-item"
    }
}

class RibbonTab(title: String?=null) : Tab(title) {
    val ribbonGroups = FXCollections.observableArrayList<RibbonGroup?>()

    private var content: HBox? = null
    var contextualColor: String? = null
        set(color) {
            field = color
            styleClass.add(color)
        }

    init {
        content = HBox()
        //        content.setMinHeight(CONTENT_HEIGHT);
        setContent(content)
        isClosable = false
        ribbonGroups.addListener(ListChangeListener<RibbonGroup> { c -> groupsChanged(c) })
        content!!.styleClass.setAll(DEFAULT_STYLE_CLASS, "tab")
        styleClass.addListener { c: ListChangeListener.Change<out String?> ->
            while (c.next()) {
                if (c.wasAdded()) {
                    for (style in c.addedSubList) {
                        content!!.styleClass.add(style)
                    }
                }
            }
        }
    }

    private fun groupsChanged(changed: ListChangeListener.Change<out RibbonGroup?>) {
        while (changed.next()) {
            if (changed.wasAdded()) {
                updateAddedGroups(changed.addedSubList)
            }
            if (changed.wasRemoved()) {
                for (group in changed.removed) {
                    val groupIndex = content!!.children.indexOf(group)
                    if (groupIndex != 0) content!!.children.removeAt(groupIndex - 1) // Remove separator
                    content!!.children.remove(group)
                }
            }
        }
    }

    private fun updateAddedGroups(addedSubList: List<RibbonGroup?>) {
        for (group in addedSubList) {
            content!!.children.add(group)
        }
    }


    companion object {
        //    public static final int CONTENT_HEIGHT = 70;
        private const val DEFAULT_STYLE_CLASS = "ribbon-tab"
    }
}

class RibbonSkin(control: Ribbon) : SkinBase<Ribbon?>(control) {
    private val outerContainer: VBox
    private val tabPane: TabPane

    /**
     * Constructor for all SkinBase instances.
     *
     * @param control The control for which this Skin should attach to.
     */
    init {
        tabPane = TabPane()
        outerContainer = VBox()

        control.tabs.addListener(ListChangeListener<RibbonTab?> { c -> tabsChanged(c) })
        //control.tabs.addListener { changed: ListChangeListener.Change<out E?> -> tabsChanged(changed) }

        updateAddedRibbonTabs(control.tabs)
        outerContainer.styleClass.setAll("outer-container")
        outerContainer.children.addAll(control.quickAccessBar, tabPane)
        children.add(outerContainer)
        control.selectedRibbonTabProperty()
            .addListener { observable: ObservableValue<*>?, oldValue: Any?, newValue: Any? ->
                tabPane.selectionModel.select(newValue as RibbonTab?)
            }
        tabPane.selectionModel.selectedItemProperty()
            .addListener { observable: ObservableValue<out Tab?>?, oldValue: Tab?, newValue: Tab? ->
                control.selectedRibbonTab.set(tabPane.selectionModel.selectedItem as RibbonTab)
            }
    }

    private fun updateAddedRibbonTabs(ribbonTabs: Collection<RibbonTab?>) {
        for (ribbonTab in ribbonTabs) tabPane.tabs.add(ribbonTab)
    }

    private fun tabsChanged(changed: ListChangeListener.Change<out RibbonTab?>) {
        while (changed.next()) {
            if (changed.wasAdded()) {
                updateAddedRibbonTabs(changed.addedSubList)
            }
            if (changed.wasRemoved()) {
                for (ribbonTab in changed.removed) tabPane.tabs.remove(ribbonTab)
            }
        }
    }
}


class QuickAccessBarSkin(control: QuickAccessBar) : SkinBase<QuickAccessBar?>(control) {
    private val outerContainer: BorderPane
    private val buttonContainer: HBox
    private val rightButtons: HBox

    /**
     * Constructor for all SkinBase instances.
     *
     * @param control The control for which this Skin should attach to.
     */
    init {
        buttonContainer = HBox()
        rightButtons = HBox()
        outerContainer = BorderPane()
        buttonContainer.styleClass.add("button-container")
        outerContainer.styleClass.add("outer-container")
        outerContainer.center = buttonContainer
        outerContainer.right = rightButtons
        children.add(outerContainer)
        updateAddedButtons(control.buttons)
    }

    private fun buttonsChanged(changed: ListChangeListener.Change<out Button>) {
        while (changed.next()) {
            if (changed.wasAdded()) {
                updateAddedButtons(changed.addedSubList)
            }
            if (changed.wasRemoved()) {
                for (button in changed.removed) buttonContainer.children.remove(button)
            }
        }
    }

    private fun updateAddedButtons(addedSubList: Collection<Button>) {
        val skinnable = skinnable
        for (button in skinnable!!.buttons) {
            buttonContainer.children.add(button)
        }
        for (button in skinnable.rightButtons) rightButtons.children.add(button)
    }
}

class RibbonItemSkin(control: RibbonItem) : SkinBase<RibbonItem?>(control) {
    private val borderPane: BorderPane
    private val label: Label

    /**
     * Constructor for all SkinBase instances.
     *
     * @param control The control for which this Skin should attach to.
     */
    init {
        borderPane = BorderPane()
        label = Label()
        control.graphicProperty
            .addListener { observable: ObservableValue<*>?, oldValue: Any?, newValue: Any? -> graphicChanged() }
        control.labelProperty
            .addListener { observable: ObservableValue<out String?>?, oldValue: String?, newValue: String? -> labelChanged() }
        control.itemProperty
            .addListener { observable: ObservableValue<*>?, oldValue: Any?, newValue: Any? -> itemChanged() }
        if (control.label != null) label.text = control.label
        if (control.graphic != null) label.graphic = control.graphic
        addLabel()
        val stackPane = StackPane()
        stackPane.children.add(control.item)
        borderPane.right = stackPane
        children.add(borderPane)
    }

    private fun itemChanged() {
        val item = skinnable!!.item
        if (item != null) {
            val stackPane = StackPane()
            stackPane.children.add(item)
            borderPane.right = stackPane
        }
    }

    private fun labelChanged() {
        val labelText = skinnable!!.label
        label.text = labelText
        addLabel()
    }

    private fun graphicChanged() {
        val graphic = skinnable!!.graphic
        if (graphic != null) {
            label.graphic = skinnable!!.graphic
            addLabel()
        }
    }

    private fun addLabel() {
        if (borderPane.left == null) {
            val stackPane = StackPane()
            stackPane.children.add(label)
            borderPane.left = stackPane
        }
    }
}

class RibbonGroupSkin(control: RibbonGroup) : SkinBase<RibbonGroup?>(control) {
    private val content: HBox
    private val container: HBox
    private val title: Label

    /**
     * Constructor for all SkinBase instances.
     *
     * @param control The control for which this Skin should attach to.
     */
    init {
        content = HBox()
        content.alignment = Pos.TOP_CENTER
        content.spacing = DEFAULT_SPACING.toDouble()
        val separator = Separator(Orientation.VERTICAL)
        container = HBox()
        title = Label()
        val titleContainer = StackPane()
        titleContainer.children.add(title)
        title.textProperty().bind(control.textProperty())
        titleContainer.styleClass.setAll("title-container")
        title.styleClass.setAll("title")
        control.nodes.addListener(ListChangeListener { changed -> buttonsChanged(changed) })
        updateAddedButtons(control.nodes)
        val vBox = VBox()
        vBox.children.addAll(content, titleContainer)
        container.children.addAll(vBox, separator)
        children.add(container)
        content.styleClass.setAll("ribbon-group-content")
    }

    private fun updateAddedButtons(nodes: Collection<Node?>) {
        for (node in nodes) content.children.add(node)
    }

    private fun buttonsChanged(changed: ListChangeListener.Change<out Node?>) {
        while (changed.next()) {
            if (changed.wasAdded()) {
                updateAddedButtons(changed.addedSubList)
            }
            if (changed.wasRemoved()) {
                for (node in changed.removed) content.children.remove(node)
            }
        }
    }

    companion object {
        private const val DEFAULT_SPACING = 0
    }
}
