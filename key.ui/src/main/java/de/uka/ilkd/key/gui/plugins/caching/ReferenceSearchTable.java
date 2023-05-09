package de.uka.ilkd.key.gui.plugins.caching;

import java.awt.*;
import java.util.List;
import javax.swing.*;
import javax.swing.event.TableModelEvent;
import javax.swing.event.TableModelListener;
import javax.swing.table.TableCellRenderer;
import javax.swing.table.TableColumn;
import javax.swing.table.TableColumnModel;
import javax.swing.table.TableModel;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ClosedBy;

class ReferenceSearchTable extends JTable implements TableModel {

    private static final long serialVersionUID = 1L;

    private final Proof proof;
    private final List<Goal> openGoals;

    @Override
    public void addTableModelListener(TableModelListener l) {

    }

    @Override
    public void removeTableModelListener(TableModelListener l) {

    }

    @Override
    public int getRowCount() {
        return openGoals.size();
    }

    @Override
    public int getColumnCount() {
        return 2;
    }

    @Override
    public String getColumnName(int column) {
        switch (column) {
        case 0:
            return "Goal";
        case 1:
            return "Reference";
        default:
            return "??";
        }
    }

    @Override
    public Class<?> getColumnClass(int column) {
        return String.class;
    }

    @Override
    public Object getValueAt(int row, int column) {
        if (column == 0) {
            return "" + openGoals.get(row).node().serialNr();
        } else {
            Goal g = openGoals.get(row);
            ClosedBy c = g.node().lookup(ClosedBy.class);
            if (c == null) {
                return "no reference found";
            } else {
                return "reference available";
            }
        }
    }


    public ReferenceSearchTable(Proof proof) {
        this.setModel(this);
        this.proof = proof;
        this.openGoals = proof.openGoals().toList();
        getColumnModel().getColumn(1).setMinWidth(200);
    }

    // @Override
    // public Dimension getPreferredSize() {
    // Dimension dim = new Dimension(super.getPreferredSize());
    // dim.height = Math.min(NUMBER_OF_VISIBLE_ROWS *
    // (progressPanelRenderer.getPreferredSize().height+5), dim.height);
    // return dim;
    // }

    public static void packColumn(JTable table, int vColIndex, int margin) {

        TableColumnModel colModel = table.getColumnModel();
        TableColumn col = colModel.getColumn(vColIndex);
        int width = 0;


        TableCellRenderer renderer = col.getHeaderRenderer();
        if (renderer == null) {
            renderer = table.getTableHeader().getDefaultRenderer();
        }
        Component comp =
            renderer.getTableCellRendererComponent(table, col.getHeaderValue(), false, false, 0, 0);
        width = comp.getPreferredSize().width;


        for (int r = 0; r < table.getRowCount(); r++) {
            renderer = table.getCellRenderer(r, vColIndex);
            comp = renderer.getTableCellRendererComponent(table, table.getValueAt(r, vColIndex),
                false, false, r, vColIndex);
            width = Math.max(width, comp.getPreferredSize().width);
        }

        width += 10 * margin;

        col.setPreferredWidth(width);
    }


    @Override
    public void tableChanged(TableModelEvent e) {
        if (e.getType() == TableModelEvent.UPDATE) {
            this.repaint();

        }
        super.tableChanged(e);
    }

}
