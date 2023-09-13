package view

import de.uka.ilkd.key.java.Services
import de.uka.ilkd.key.speclang.Contract
import javafx.beans.property.ObjectProperty
import javafx.beans.value.ObservableValue
import javafx.collections.ObservableList
import javafx.event.EventHandler
import javafx.scene.control.*
import javafx.scene.input.KeyEvent
import javafx.scene.text.Text
import javafx.scene.text.TextFlow
import javafx.stage.Modality
import kotlin.jvm.optionals.getOrNull


/**
 * A Contract Chooser is a modal dialog, which shows a list of contracts and lets the user select one.
 * WizardPane to display all available contracts
 *
 * @author S. Grebing
 * @author A. Weigl
 */
fun chooseContract(services: Services, contracts: List<Contract>): Contract? {
    val dialog = Dialog<Contract>()

    val listOfContractsView = ListView<Contract>().also {
        it.items.setAll(contracts)
        it.setCellFactory { contractListView: ListView<Contract> -> ContractListCell(services, contractListView) }
    }
    var selectionModel: MultipleSelectionModel<Contract> = listOfContractsView.selectionModel
    val itemsProperty: ObjectProperty<ObservableList<Contract>> = listOfContractsView.itemsProperty()

    dialog.title = "Key Contract Chooser"
    dialog.headerText = "Please select a contract"
    dialog.isResizable = true
    dialog.initModality(Modality.APPLICATION_MODAL)
    selectionModel = listOfContractsView.selectionModel
    val dpane = DialogPane()
    dpane.content = listOfContractsView
    dpane.setPrefSize(680.0, 320.0)
    dialog.dialogPane = dpane

    listOfContractsView.setCellFactory { view: ListView<Contract?> ->
        ContractListCell(services, listOfContractsView)
    }

    dialog.setResultConverter { value ->
        if (value === ButtonType.OK) listOfContractsView.selectionModel.selectedItem else null
    }
    dpane.buttonTypes.addAll(ButtonType.OK, ButtonType.CANCEL)

    val okButton = dpane.lookupButton(ButtonType.OK) as Button
    okButton.isDefaultButton = true

    listOfContractsView.onKeyPressed = EventHandler { event: KeyEvent? -> okButton.fire() }

    dpane.buttonTypes.addAll(ButtonType.OK, ButtonType.CANCEL)
    listOfContractsView.onKeyPressed = EventHandler { okButton.fire() }
    return dialog.showAndWait().getOrNull()
}

private class ContractListCell(val services: Services, contractListView: ListView<Contract>) : ListCell<Contract?>() {
    private val text = TextFlow()

    init {
        itemProperty().addListener { observable: ObservableValue<out Contract?>?, oldValue: Contract?, newValue: Contract? -> render() }
        selectedProperty().addListener { observable: ObservableValue<out Boolean?>?, oldValue: Boolean?, newValue: Boolean? -> render() }
        text.maxWidthProperty().bind(contractListView.widthProperty())
        graphic = text
    }

    private fun render() {
        if (item != null) {
            text.children.clear()
            val content = item!!.getPlainText(services)
            val contract = Text("Contract for method: ")
            val name = Text(item!!.getTarget().toString())
            val tcontent = Text(content)
            contract.style = "-fx-font-weight: bold; -fx-font-size: 120%"
            name.style = "-fx-font-family: monospace; -fx-font-size: 120%"
            tcontent.style = "-fx-font-family: monospace"
            text.children.add(contract)
            text.children.add(name)
            text.children.add(Text("\n"))
            //text.getChildren().addCell(tcontent);
            for (line in content.split("\n".toRegex()).dropLastWhile { it.isEmpty() }.toTypedArray()) {
                if (line.contains(":")) {
                    val a = line.split(":".toRegex(), limit = 2).toTypedArray()
                    val s = Text(String.format("%-15s", a[0] + ":"))
                    val t = Text(a[1] + "\n")
                    s.style = "-fx-font-family: monospace;-fx-font-weight:bold;-fx-min-width: 10em"
                    t.style = "-fx-font-family: monospace"
                    text.children.addAll(s, t)
                } else {
                    val t = Text(line + "\n")
                    t.style = "-fx-font-family: monospace"
                    text.children.addAll(t)
                }
            }
            if (selectedProperty().get()) {
                //   text.setStyle("-fx-background-color: lightblue");
            }
        }
    }

    private fun beautifyContractHTML(html: String, name: String): String {
        return "Contract for <b>$name</b><br>$html"
    }
}