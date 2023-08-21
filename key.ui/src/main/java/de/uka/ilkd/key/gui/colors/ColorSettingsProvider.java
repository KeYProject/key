/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.colors;

import java.awt.*;
import java.awt.image.BufferedImage;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.table.AbstractTableModel;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.TableRowSorter;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.gui.settings.SimpleSettingsPanel;

/**
 * @author Alexander Weigl
 * @version 1 (10.05.19)
 */
public class ColorSettingsProvider extends SimpleSettingsPanel implements SettingsProvider {
    private static final long serialVersionUID = -6253991459166324512L;
    private final JTable tblColors = new JTable();
    private ColorSettingsTableModel modelColor;

    public ColorSettingsProvider() {
        super();
        setHeaderText(getDescription());
        setSubHeaderText(
            "Color settings are stored in: " + ColorSettings.SETTINGS_FILE.getAbsolutePath());
        add(new JScrollPane(tblColors));
    }

    @Override
    public String getDescription() {
        return "Colors";
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        List<ColorPropertyData> properties = ColorSettings.getInstance().getProperties()
                .map(it -> new ColorPropertyData(it, it.get())).collect(Collectors.toList());

        modelColor = new ColorSettingsTableModel(properties);
        tblColors.setModel(modelColor);

        // tblColors.getColumnModel().getColumn(2).setCellEditor(new ColorChooserEditor());

        TableRowSorter<ColorSettingsTableModel> sorter = new TableRowSorter<>(modelColor);
        tblColors.setRowSorter(sorter);

        List<RowSorter.SortKey> sortKeys = new ArrayList<>(25);
        sortKeys.add(new RowSorter.SortKey(0, SortOrder.ASCENDING));
        sorter.setSortKeys(sortKeys);

        tblColors.getColumnModel().getColumn(2).setCellEditor(HexColorCellEditor.make());

        tblColors.setDefaultRenderer(Color.class, new DefaultTableCellRenderer() {
            private static final long serialVersionUID = -7602735597024671100L;

            @Override
            public Component getTableCellRendererComponent(JTable table, Object value,
                    boolean isSelected, boolean hasFocus, int row, int column) {
                Color c = (Color) value;
                String s = ColorSettings.toHex(c);
                JLabel lbl = (JLabel) super.getTableCellRendererComponent(table, s, isSelected,
                    hasFocus, row, column);
                lbl.setIcon(drawRect(c, lbl.getFont().getSize()));
                return lbl;
            }

            private Icon drawRect(Color c, int size) {
                BufferedImage bi = new BufferedImage(size, size, BufferedImage.TYPE_INT_RGB);
                Graphics g = bi.getGraphics();
                g.setColor(c);
                g.fillRect(0, 0, size, size);
                return new ImageIcon(bi);
            }
        });

        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        modelColor.colorData.forEach(it -> it.property.set(it.color));
    }

    private static class ColorSettingsTableModel extends AbstractTableModel {
        private static final long serialVersionUID = 4722928883386296559L;
        private static final String[] COLUMNS = new String[] { "Key", "Description", "Color" };
        private final List<ColorPropertyData> colorData;

        public ColorSettingsTableModel(List<ColorPropertyData> properties) {
            colorData = properties;
        }

        @Override
        public int getRowCount() {
            return colorData.size();
        }

        @Override
        public int getColumnCount() {
            return COLUMNS.length;
        }

        @Override
        public String getColumnName(int column) {
            return COLUMNS[column];
        }

        @Override
        public Object getValueAt(int rowIndex, int columnIndex) {
            switch (columnIndex) {
            case 0:
                return colorData.get(rowIndex).property.getKey();
            case 1:
                return colorData.get(rowIndex).property.getDescription();
            case 2:
                return colorData.get(rowIndex).color;
            }
            return "";
        }

        @Override
        public Class<?> getColumnClass(int columnIndex) {
            if (columnIndex == 2) {
                return Color.class;
            }
            return String.class;
        }

        @Override
        public void setValueAt(Object aValue, int rowIndex, int columnIndex) {
            if (columnIndex == 2) {
                colorData.get(rowIndex).color = ColorSettings.fromHex(aValue.toString());
            } else {
                super.setValueAt(aValue, rowIndex, columnIndex);
            }
        }

        @Override
        public boolean isCellEditable(int rowIndex, int columnIndex) {
            return columnIndex == 2;
        }
    }

    private static class ColorPropertyData {
        private final ColorSettings.ColorProperty property;
        Color color;

        public ColorPropertyData(ColorSettings.ColorProperty property, Color color) {
            this.property = property;
            this.color = color;
        }
    }


}


class HexColorCellEditor extends DefaultCellEditor {
    private static final long serialVersionUID = -4352607386521686931L;

    HexColorCellEditor(JTextField textField) {
        super(textField);
        textField.addActionListener(e -> stopCellEditing());
        textField.getDocument().addDocumentListener(new DocumentListener() {
            @Override
            public void insertUpdate(DocumentEvent e) {
                updateBackground();
            }

            @Override
            public void removeUpdate(DocumentEvent e) {
                updateBackground();

            }

            @Override
            public void changedUpdate(DocumentEvent e) {
                updateBackground();

            }

            private void updateBackground() {
                try {
                    Color c = ColorSettings.fromHex(textField.getText());
                    textField.setBackground(c);
                    textField.setForeground(ColorSettings.invert(c));
                } catch (NumberFormatException ignored) {

                }
            }
        });
    }

    public static HexColorCellEditor make() {
        JTextField field = new JTextField();
        field.setBorder(null);
        return new HexColorCellEditor(field);
    }

    @Override
    public Component getTableCellEditorComponent(JTable table, Object value, boolean isSelected,
            int row, int column) {
        Component txt = super.getTableCellEditorComponent(table, ColorSettings.toHex((Color) value),
            isSelected, row, column);
        Color c = (Color) value;
        txt.setBackground(c);
        txt.setForeground(ColorSettings.invert(c));
        return txt;
    }
}

/*
 * FROM: http://www.java2s.com/Tutorial/Java/0240__Swing/ColorChooserEditor.htm /*class
 * ColorChooserEditor extends AbstractCellEditor implements TableCellEditor { private Color
 * savedColor; private JButton delegate = new JButton();
 *
 * public ColorChooserEditor() { ActionListener actionListener = actionEvent -> { Color color =
 * JColorChooser.showDialog(delegate, "Color Chooser", savedColor);
 * ColorChooserEditor.this.changeColor(color); }; delegate.addActionListener(actionListener); }
 *
 * public Object getCellEditorValue() { return savedColor; }
 *
 * private void changeColor(Color color) { if (color != null) { savedColor = color;
 * delegate.setBackground(color); } }
 *
 * public Component getTableCellEditorComponent(JTable table, Object value, boolean isSelected, int
 * row, int column) { changeColor((Color) value); return delegate; } }
 */
