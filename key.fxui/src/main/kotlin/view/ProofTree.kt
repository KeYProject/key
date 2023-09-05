package io.github.wadoon.key.view

import javafx.scene.control.TreeItem
import org.kordamp.ikonli.javafx.FontIcon
import org.kordamp.ikonli.material2.Material2AL
import tornadofx.View
import tornadofx.toolbar
import tornadofx.treeview
import tornadofx.vbox

class ProofTree : View("Proof Tree", FontIcon(Material2AL.ACCOUNT_TREE)) {
    override val root = vbox {
        toolbar()
        treeview(TreeItem<String>("No proof loaded")) { }
    }
}