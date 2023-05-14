package de.uka.ilkd.key.gui.plugins.caching;

import java.util.List;
import javax.swing.*;
import javax.swing.event.TableModelEvent;
import javax.swing.event.TableModelListener;
import javax.swing.table.TableModel;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ClosedBy;

class ReferenceSearchTable extends JTable implements TableModel {

    private static final long serialVersionUID = 1L;

    private final KeYMediator mediator;
    private final Proof proof;
    private final List<Goal> openGoals;

    public ReferenceSearchTable(Proof proof, KeYMediator mediator) {
        this.setModel(this);
        this.proof = proof;
        this.openGoals = proof.openGoals().toList();
        this.mediator = mediator;
        getColumnModel().getColumn(1).setMinWidth(200);
    }

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
                int i = mediator.getCurrentlyOpenedProofs().indexOf(c.getProof()) + 1;
                return String.format("reference available (proof %d)", i);
            }
        }
    }

    @Override
    public boolean isCellEditable(int row, int column) {
        return false;
    }

    @Override
    public void tableChanged(TableModelEvent e) {
        if (e.getType() == TableModelEvent.UPDATE) {
            this.repaint();

        }
        super.tableChanged(e);
    }

}
