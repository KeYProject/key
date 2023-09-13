package io.github.wadoon.key.view

import javafx.scene.control.Label
import org.kordamp.ikonli.Ikon
import org.kordamp.ikonli.javafx.FontIcon
import tornadofx.FXEvent
import tornadofx.View
import tornadofx.getValue
import tornadofx.setValue

/**
 *
 * @author Alexander Weigl
 * @version 1 (11.09.23)
 */
class StatusBar : View() {
    override val root = Label()

    val graphicProperty = root.graphicProperty()
    var graphic by graphicProperty

    val textProperty = root.textProperty()
    var text by textProperty

    init {
        subscribe<SetStatusBar> {
            it.icon?.let { graphic = FontIcon(it) }
            text = it.text
        }
    }
}

data class SetStatusBar(val text: String, val icon: Ikon? = null) : FXEvent()
