package edu.kit.iti.formal.keyextclientjava;

import javafx.geometry.Orientation;
import javafx.scene.control.*;
import javafx.scene.layout.BorderPane;
import javafx.stage.FileChooser;
import org.controlsfx.glyphfont.FontAwesome;
import org.kordamp.ikonli.Ikon;
import org.kordamp.ikonli.fontawesome5.FontAwesomeRegular;
import org.kordamp.ikonli.javafx.FontIcon;

import javax.swing.*;
import java.io.IOException;
import java.util.concurrent.ForkJoinPool;

/**
 * @author Alexander Weigl
 * @version 1 (22.11.24)
 */
public class MyKeyClient {
    private static final String JAR_FILE = "";
    private final ToolBar toolbar = new ToolBar();
    private final Label txtStatus = new Label("Yeah!");
    public final BorderPane root = new BorderPane();
    private final TreeView<TreeNodeId> tnid = new TreeView<>();
    private final TextArea txtSequentView = new TextArea();

    private final FileChooser fc = new FileChooser();

    public MyKeyClient() {
        //region toolbar
        var btnOpen = new Button("Open", new FontIcon(FontAwesomeRegular.FOLDER_OPEN));
        btnOpen.setOnAction(actionEvent -> openFile());
        toolbar.getItems().setAll(btnOpen, new Separator(Orientation.VERTICAL));
        //endregion

        var splitCenter = new SplitPane(tnid, txtSequentView);
        splitCenter.setDividerPositions(.2);
        root.setTop(toolbar);
        root.setCenter(splitCenter);
        root.setBottom(txtStatus);

        var startKey = ForkJoinPool.commonPool().submit(this::startKey);
    }

    private Object startKey() throws IOException {
        return new KeyRemote(RPCLayer.startWithCLI(JAR_FILE));

    }

    private void openFile() {
        fc.showOpenDialog(null);
    }
}
