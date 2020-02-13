// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.gui.actions.EditSourceFileAction;
import de.uka.ilkd.key.gui.actions.SendFeedbackAction;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.SVInstantiationExceptionWithPosition;
import de.uka.ilkd.key.util.ExceptionTools;
import org.key_project.util.java.StringUtil;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Dialog to display error messages.
 *
 * @author refactored by mattias
 */
public class ExceptionDialog extends JDialog {

    public final static Font MESSAGE_FONT = new Font(Font.MONOSPACED, Font.PLAIN, 12);

    private static final long serialVersionUID = -4532724315711726522L;
    private JScrollPane stScroll;
    private JTextArea stTextArea;

    private Location location;
    private Throwable exception;

    public static void showDialog(Window parent, Throwable exception) {
        ExceptionDialog dlg = new ExceptionDialog(parent, exception);
            dlg.setVisible(true);
            dlg.dispose();
        }

    private ExceptionDialog(Window parent, Throwable exception) {
        super(parent, "Parser Messages", Dialog.ModalityType.DOCUMENT_MODAL);
        this.exception = exception;
        this.location = ExceptionTools.getLocation(exception);
        init();
    }

    private JPanel createButtonPanel() {
        ActionListener closeListener = new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                setVisible(false);
            }
        };

        ItemListener detailsBoxListener = new ItemListener() {
            @Override
            public void itemStateChanged(ItemEvent e) {
                Container contentPane = getContentPane();
                if (e.getStateChange() == ItemEvent.SELECTED){
                    contentPane.add(stScroll, new GridBagConstraints(0, 3, 1, 1, 1., 10.,
                            GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(
                                    0, 0, 0, 0), 0, 0));
                } else {
                    contentPane.remove(stScroll);
                }
                pack();
                // setLocationRelativeTo(null);
                contentPane.repaint();
            }
        };

        JButton reloadButton = new JButton("Reload");
        reloadButton.setAction(MainWindow.getInstance().getOpenMostRecentFileAction());
        reloadButton.addActionListener(closeListener);

        JButton closeButton = new JButton("Close");
        closeButton.addActionListener(closeListener);
        getRootPane().setDefaultButton(closeButton);

        JCheckBox detailsBox  = new JCheckBox("Show Details");
        detailsBox.setSelected(false);
        detailsBox.addItemListener(detailsBoxListener);

        JPanel bPanel = new JPanel();
//        bPanel.add(reloadButton); // XXX useful for debugging

        JButton sendFeedbackButton = new JButton(new SendFeedbackAction(this, exception));
           bPanel.add(sendFeedbackButton);

        JButton editSourceFileButton = new JButton("Edit Source File");
        EditSourceFileAction action = new EditSourceFileAction(this, exception);
        editSourceFileButton.addActionListener(action);
        if(!action.isValidLocation(location)) {
            editSourceFileButton.setEnabled(false);
        }
        bPanel.add(editSourceFileButton);
        
        bPanel.add(closeButton);
        bPanel.add(detailsBox);

        return bPanel;
    }

    private JScrollPane createStacktraceTextAreaScroll() {
        JScrollPane scroll = new JScrollPane(stTextArea);
        scroll.setBorder(new TitledBorder("Stack Trace"));
        scroll.setPreferredSize(new Dimension(500, 300));
        return scroll;
    }

    private JTextArea createStacktraceTextArea() {
        JTextArea result = new JTextArea();
        result.setEditable(false);
        result.setTabSize(4);
        result.setFont(MESSAGE_FONT);
        return result;
    }

    private void setStackTraceText() {
        StringWriter sw = new StringWriter();
        // sw.append("(").append(exc.getClass().toString()).append(")\n");
        PrintWriter pw = new PrintWriter(sw);
        exception.printStackTrace(pw);
        stTextArea.setText(sw.toString());
    }

    private JScrollPane createExcTextAreaScroll() {
        JTextArea exTextArea = createStacktraceTextArea();
        Dimension textPaneDim = new Dimension(500, 200);
        exTextArea.setColumns(120);
        exTextArea.setLineWrap(true);
        exTextArea.setWrapStyleWord(true);

        String orgMsg = exception.getMessage();
        if(orgMsg == null){
            orgMsg = "";
        }
        StringBuilder message = new StringBuilder(orgMsg);

        Location loc = location;
        if(loc != null && loc.getFilename() != null && !"".equals(loc.getFilename())
                && !"no file".equals(loc.getFilename())) {
            try {
                // read the content via URLs openStream() method
                BufferedReader br = new BufferedReader(new InputStreamReader(
                        loc.getFileURL().openStream()));
                List<String> list = br.lines()
                                      // optimization: read only as far as necessary
                                      .limit(loc.getLine())
                                      .collect(Collectors.toList());
                String line = list.get(loc.getLine() - 1);
                String pointLine = StringUtil.createLine(" ", loc.getColumn() - 1) + "^";
                message.append(StringUtil.NEW_LINE).
                    append(StringUtil.NEW_LINE).
                    append(line).
                    append(StringUtil.NEW_LINE).
                    append(pointLine);
            } catch (Exception e) {
                System.err.println("Creating an error line did not work for " + loc);
                e.printStackTrace();
            }
        }

        exTextArea.setText(message.toString());
        exTextArea.setTabSize(2);

        // ensures that the dialog shows the error messaged scrolled to its start
        exTextArea.setCaretPosition(0);

        JScrollPane scroll = new JScrollPane(exTextArea);
        scroll.setBorder(new TitledBorder(exception.getClass().getName()));
        scroll.setPreferredSize(textPaneDim);

        return scroll;
    }

    // returns null if no location can be extracted.
    private JPanel createLocationPanel() {
	Location loc = location;

	if (loc == null) {
	    return null;
	}

	JPanel lPanel = new JPanel();
	JTextField fTextField, lTextField, cTextField;
	fTextField = new JTextField();
	lTextField = new JTextField();
	cTextField = new JTextField();
	fTextField.setEditable(false);
	lTextField.setEditable(false);
	cTextField.setEditable(false);


	if ( !( loc.getFilename()==null || "".equals(loc.getFilename()))) {
	    fTextField.setText("File: " + loc.getFilename());
	    lPanel.add(fTextField);
	}

	if (exception instanceof SVInstantiationExceptionWithPosition) {
	    lTextField.setText("Row: " + loc.getLine());
	} else {
	    lTextField.setText("Line: " + loc.getLine());
	}

	lPanel.add(lTextField);

	cTextField.setText("Column: " + loc.getColumn());
	lPanel.add(cTextField);

	return lPanel;
    }

    private void init() {

        Container cp = getContentPane();
        cp.setLayout(new GridBagLayout());

        cp.add(createExcTextAreaScroll(),
                    new GridBagConstraints(0, 0, 1, 1, 1., 1e-10,
                    GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(
                            0, 0, 0, 0), 0, 0));

        JPanel locationPanel = createLocationPanel();

        if(locationPanel != null) {
            cp.add(locationPanel, new GridBagConstraints(0, 1, 1, 1, 1., 0.,
                    GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(
                            0, 0, 0, 0), 0, 0));
        }

        JPanel buttonPanel = createButtonPanel();
        cp.add(buttonPanel, new GridBagConstraints(0, 2, 1, 1, 1., 0.,
                GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(
                        0, 0, 0, 0), 0, 0));

        // not displayed, only created;
        stTextArea = createStacktraceTextArea();
        stScroll = createStacktraceTextAreaScroll();
        setStackTraceText();

        setDefaultCloseOperation(DISPOSE_ON_CLOSE);
        pack();
        setLocationRelativeTo(null);
    }

// in earlier versions, KeY supported several exceptions.

//    private JScrollPane createJListScroll(final List<Throwable> exceptions) {
//         Vector<String> excMessages = new Vector<String>();
//         int i = 1;
//         for (Throwable throwable : exceptions) {
//            Location location = ExceptionTools.getLocation(throwable);
//            if(location != null) {
//                excMessages.add(i + ") Location: " +  location + "\n" + throwable.getMessage());
//            } else {
//                excMessages.add(i + ") " + throwable.getMessage());
//            }
//            i ++;
//         }
//
//         final JList list = new JList(excMessages);
//         list.setCellRenderer(new TextAreaRenderer());
//         list.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
//         list.setSelectedIndex(0);
//
//         JScrollPane elistScroll =
//             new JScrollPane(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
//                     ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
//         elistScroll.getViewport().setView(list);
//         elistScroll.setBorder(new TitledBorder("Exceptions/Errors"));
//         elistScroll.setPreferredSize(new Dimension(500, 300));
//         ListSelectionListener listListener = new ListSelectionListener() {
//             public void valueChanged(ListSelectionEvent e) {
//                 Throwable exc = exceptions.get(list.getSelectedIndex());
//                 setStackTraceText(exc);
//             }
//         };
//
//         list.addListSelectionListener(listListener);
//         return elistScroll;
//
//    }
//
//    private static class TextAreaRenderer
//      extends JTextArea implements ListCellRenderer<String> {
//        /**
//         *
//         */
//        private static final long serialVersionUID = -1151786934514170956L;
//
//        public TextAreaRenderer()
//        {
//            setLineWrap(true);
//	    setWrapStyleWord(true);
//	    // setRows(10);
//        }
//
//        public Component getListCellRendererComponent(JList<? extends String> list, String value,
//            int index, boolean isSelected, boolean cellHasFocus)
//        {
//            // if (index==0) setFont(getFont().deriveFont(Font.BOLD, 12)); else
//	    setFont(getFont().deriveFont(Font.PLAIN, 12));
//            setText(value.toString());
//            setBackground(isSelected ? list.getSelectionBackground() : null);
//            setForeground(isSelected ? list.getSelectionForeground() : null);
//            return this;
//        }
//    }

}