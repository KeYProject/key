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

package de.uka.ilkd.key.gui.smt;

import java.awt.Color;
import java.util.ArrayList;

import javax.swing.table.AbstractTableModel;

/**
 * Encapsulates the table of progress bars that is shown within the progress dialog:
 * For each solver and each goal there is a cell.  
 */
class ProgressModel extends AbstractTableModel {
        private static final long serialVersionUID = 1L;

        private static interface Column {
                Object getObject(int row);

                int getRowCount();

                boolean isEditable();

        }

        public static class TitleColumn implements Column {
                private final String[] titles;

                public TitleColumn(String... titles) {
                        super();
                        this.titles = titles;

                }

                @Override
                public Object getObject(int row) {
                        return titles[row];
                }

                @Override
                public int getRowCount() {

                        return titles.length;
                }

                @Override
                public boolean isEditable() {

                        return false;
                }

        }

        public static class ProcessColumn implements Column {

                static class ProcessData {
                        private int progress = 0;
                        private String text = "";
                        private boolean isEditable = false;
                        private Color textColor = Color.BLACK;
                        private Color backgroundColor = Color.WHITE;
                        private Color foregroundColor = Color.BLUE;
                        private Color selectedTextColor = Color.WHITE;

                        public int getProgress() {
                                return progress;
                        }

                        public String getText() {
                                return text;
                        }

                        public boolean isEditable() {
                                return isEditable;
                        }

                        public Color getBackgroundColor() {
                                return backgroundColor;
                        }

                        public Color getSelectedTextColor() {
                                return selectedTextColor;
                        }

                        public Color getTextColor() {
                                return textColor;
                        }

                        public Color getForegroundColor() {
                                return foregroundColor;
                        }

                }

                // private final Object [] processes;
                public final ProcessData[] data;
                private boolean isEditable = false;

                public ProcessColumn(int size) {
                        super();

                        this.data = new ProcessData[size];

                        for (int i = 0; i < data.length; i++) {
                                data[i] = new ProcessData();

                        }

                }

                @Override
                public Object getObject(int row) {

                        return data[row];
                }

                public void setProgress(int value, int row) {
                        data[row].progress = value;
                }

                public void setText(String value, int row) {
                        data[row].text = value;
                }

                @Override
                public int getRowCount() {

                        return data.length;
                }

                public void setEditable(boolean b) {
                        isEditable = b;
                        for (int i = 0; i < data.length; i++) {
                                data[i].isEditable = b;
                        }
                }

                @Override
                public boolean isEditable() {

                        return isEditable;
                }

        }

        private ArrayList<Column> columns = new ArrayList<Column>();

        private int rowCount = -1;

        public ProgressModel() {
                super();

        }

        public void addColumn(Column column) {
                if (rowCount != -1 && rowCount != column.getRowCount()) {
                        throw new IllegalArgumentException(
                                        "Columns must have the same number of rows.");
                }
                rowCount = column.getRowCount();
                columns.add(column);
        }

        public void setProgress(int value, int column, int row) {
                column++;
                ProcessColumn col = (ProcessColumn) columns.get(column);
                col.setProgress(value, row);
                this.fireTableCellUpdated(row, column);
        }

        public void setText(String text, int column, int row) {
                column++;
                ProcessColumn col = (ProcessColumn) columns.get(column);
                col.setText(text, row);
                this.fireTableCellUpdated(row, column);
        }

        public void setTextColor(Color color, int x, int y) {
                x++;
                ProcessColumn col = (ProcessColumn) columns.get(x);
                col.data[y].textColor = color;

                this.fireTableCellUpdated(x, y);
        }

        public void setForegroundColor(Color color, int x, int y) {
                x++;
                ProcessColumn col = (ProcessColumn) columns.get(x);
                col.data[y].foregroundColor = color;

                this.fireTableCellUpdated(x, y);
        }

        public void setBackgroundColor(Color color, int x, int y) {
                x++;
                ProcessColumn col = (ProcessColumn) columns.get(x);
                col.data[y].backgroundColor = color;
                this.fireTableCellUpdated(x, y);
        }

        public void setEditable(boolean b) {
                for (Column column : columns) {
                        if (column instanceof ProcessColumn) {
                                ((ProcessColumn) column).setEditable(b);
                        }
                }
        }

        @Override
        public int getColumnCount() {

                return columns.size();
        }

        @Override
        public int getRowCount() {

                return rowCount;
        }

        @Override
        public boolean isCellEditable(int rowIndex, int columnIndex) {

                return columns.get(columnIndex).isEditable();
        }

        @Override
        public Class<?> getColumnClass(int columnIndex) {
                return columns.get(columnIndex).getClass();

        }

        @Override
        public Object getValueAt(int row, int col) {

                return columns.get(col).getObject(row);
        }

        public Column getColumn(int col) {
                return columns.get(col);
        }

}