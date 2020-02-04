package de.uka.ilkd.key.gui.actions;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.Font;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JEditorPane;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.UIManager;
import javax.swing.filechooser.FileNameExtensionFilter;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Debug;

/**
 * Shows proof statistics and allows the user to save them as HTML or CSV.
 *
 * @author lanzinger
 */
public class ShowProofStatisticsWindow extends JFrame {

    /**
     * Creates a new (initially invisible) proof statistics window.
     *
     * @param mainWindow the main windown.
     * @param proof the proof whose statistics to show.
     */
    public ShowProofStatisticsWindow(MainWindow mainWindow, Proof proof) {
        super("Proof Statistics");

        String stats = ShowProofStatistics.getHTMLStatisticsMessage(proof);

        JEditorPane statisticsPane = new JEditorPane("text/html", stats);
        statisticsPane.setEditable(false);
        statisticsPane.setBorder(BorderFactory.createEmptyBorder());
        statisticsPane.setCaretPosition(0);
        statisticsPane.setBackground(MainWindow.getInstance().getBackground());
        statisticsPane.setSize(new Dimension(10, 360));
        statisticsPane.setPreferredSize(
                new Dimension(statisticsPane.getPreferredSize().width + 15, 360));

        JScrollPane scrollPane = new JScrollPane(statisticsPane);
        scrollPane.setBorder(BorderFactory.createEmptyBorder());

        Font myFont = UIManager.getFont(Config.KEY_FONT_PROOF_TREE);
        if (myFont != null) {
            statisticsPane.putClientProperty(JEditorPane.HONOR_DISPLAY_PROPERTIES, Boolean.TRUE);
            statisticsPane.setFont(myFont);
        } else {
            Debug.out("KEY_FONT_PROOF_TREE not available. Use standard font.");
        }

        JPanel buttonPane = new JPanel();

        JButton okButton = new JButton("OK");
        okButton.addActionListener(event -> {
            dispose();
        });

        JButton csvButton = new JButton("Export as CSV");
        csvButton.addActionListener(event -> {
            export("csv", proof.name().toString(),
                    ShowProofStatistics.getCSVStatisticsMessage(proof));
        });

        JButton htmlButton = new JButton("Export as HTML");
        htmlButton.addActionListener(event -> {
            export("html", proof.name().toString(),
                    ShowProofStatistics.getHTMLStatisticsMessage(proof));
        });

        buttonPane.add(okButton);
        buttonPane.add(csvButton);
        buttonPane.add(htmlButton);

        setLayout(new BorderLayout());
        add(scrollPane, BorderLayout.CENTER);
        add(buttonPane, BorderLayout.PAGE_END);

        int w = Math.max(
                scrollPane.getPreferredSize().width,
                buttonPane.getPreferredSize().width);
        int h = scrollPane.getPreferredSize().height;
        setSize(w, h);
        setLocationRelativeTo(mainWindow);
    }

    private void export(String fileExtension, String fileName, String text) {
        JFileChooser fileChooser = new JFileChooser();
        fileChooser.addChoosableFileFilter(new FileNameExtensionFilter(
                fileExtension.toUpperCase() + " files", fileExtension));
        fileChooser.setAcceptAllFileFilterUsed(false);
        fileChooser.setSelectedFile(new File(fileName + "." + fileExtension));
        int returnVal = fileChooser.showSaveDialog(this);
        if (returnVal == JFileChooser.APPROVE_OPTION) {
            File file = fileChooser.getSelectedFile();
            try(BufferedWriter writer = new BufferedWriter(
                        new OutputStreamWriter(new FileOutputStream(file)));) {
                writer.write(text);
            } catch (IOException e) {
                e.printStackTrace();
                assert false;
            }
        }
    }
}
